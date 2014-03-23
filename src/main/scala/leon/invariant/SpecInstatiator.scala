package leon
package invariant

import scala.util.Random
import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import leon.evaluators._
import java.io._
import leon.solvers.z3.UninterpretedZ3Solver
import leon.LeonContext
import leon.LeonOptionDef
import leon.LeonPhase
import leon.LeonValueOption
import leon.ListValue
import leon.Reporter
import leon.verification.DefaultTactic
import leon.verification.Tactic
import leon.verification.VerificationReport
import leon.solvers.SimpleSolverAPI
import leon.solvers.z3.UIFZ3Solver
import leon.invariant._
import leon.purescala.UndirectedGraph
import scala.util.control.Breaks._
import leon.solvers._
import scala.concurrent._
import scala.concurrent.duration._
import ExecutionContext.Implicits.global
import leon.purescala.ScalaPrinter
import leon.plugin.NonlinearityEliminationPhase

class SpecInstantiator(ctx : LeonContext, program : Program, ctrTracker : ConstraintTracker, tempFactory : TemplateFactory) {               
    
  protected val disableAxioms = false
  protected val debugAxiomInstantiation = false  
  
  val tru = BooleanLiteral(true)
  val axiomFactory = new AxiomFactory(ctx,program) //handles instantiation of axiomatic specification
  
  //the guards of the set of calls that were already processed
  protected var exploredGuards = Set[Variable]()   
 
  def instantiate() = {                 
    val funcs = ctrTracker.getFuncs     
        
    funcs.foreach((fd) => {
      val formula = ctrTracker.getVC(fd)     
      val disjuncts = formula.disjunctsInFormula
      val newguards = disjuncts.keySet.diff(exploredGuards)
      exploredGuards ++= newguards
      
      val newcalls = newguards.flatMap(g => disjuncts(g).collect { case c: Call => c })
      instantiateSpecs(formula, newcalls, funcs.toSet)
      
//      if(this.debugAxiomInstantiation) {        
//        println("Instantianting axioms over: " + newCalls)
//        val filename = "instFormula-" + FileCountGUID.getID        
//        val wr = new PrintWriter(new File(filename + ".txt"))
//        //val printableExpr = variablesOf(formula).filterNot(TVarFactory.isTemporary _))
//        ExpressionTransformer.PrintWithIndentation(wr, simpForm)        
//        wr.flush()
//        wr.close()
//        println("Printed instFormula to file: " + filename)
//      }
      if(!disableAxioms)      
    	  instantiateAxioms(formula, newcalls)      
    })    
  }  

  /**
   * This function refines the formula by assuming the specifications/templates for calls in the formula
   * Here, we assume (pre => post ^ template) for each call (templates only for calls with VC)
   * Important: adding templates for 'newcalls' of the previous iterations is empirically more effective
   */
   //a set of calls for which templates or specifications have not been assumed
  private var untemplatedCalls = Map[FunDef,Set[Call]]()
  def getUntempCalls(fd: FunDef) = if(untemplatedCalls.contains(fd)) untemplatedCalls(fd) else Set()
  def resetUntempCalls(fd: FunDef, calls: Set[Call]) = {
    if (untemplatedCalls.contains(fd)) {
      untemplatedCalls -= fd
      untemplatedCalls += (fd -> calls)
    } else {
      untemplatedCalls += (fd -> calls)
    }
  }
  
  def instantiateSpecs(formula: Formula, calls : Set[Call], funcsWithVC: Set[FunDef]) = {    

    //assume specifications    
    calls.foreach((call) => {
      //first get the spec for the call if it exists 
      val spec = specForCall(call)
      if (spec.isDefined && spec.get != tru) {
    	val cdata = formula.callData(call)
        formula.conjoinWithDisjunct(cdata.guard, spec.get, cdata.parents)                
      }
    })

    //try to assume templates for all the current un-templated calls    
    var newUntemplatedCalls = Set[Call]()    
    getUntempCalls(formula.fd).foreach((call) => {
      //first get the template for the call if one needs to be added
      if (funcsWithVC.contains(call.fi.funDef)) {
        val temp = templateForCall(call)
        val cdata = formula.callData(call)
        formula.conjoinWithDisjunct(cdata.guard, temp, cdata.parents)               
        
      } else {
        newUntemplatedCalls += call
      }
    })
    resetUntempCalls(formula.fd, newUntemplatedCalls ++ calls)        
  }

  def specForCall(call: Call): Option[Expr] = {
    val argmap = Util.formalToAcutal(call)
    val callee = call.fi.funDef
    if (callee.hasPostcondition) {
      val (resvar, post) = callee.postcondition.get
      val freshPost = freshenLocals(matchToIfThenElse(post))

      val spec = if (callee.hasPrecondition) {
        val freshPre = freshenLocals(matchToIfThenElse(callee.precondition.get))
        Implies(freshPre, freshPost)
      } else {
        freshPost
      }
      val inlinedSpec = ExpressionTransformer.normalizeExpr(replace(argmap, spec))
      Some(inlinedSpec)
    } else {
      None
    }
  }

  def templateForCall(call: Call): Expr = {
    val argmap = Util.formalToAcutal(call)
    val tempExpr = tempFactory.constructTemplate(argmap, call.fi.funDef)
    val template = if (call.fi.funDef.hasPrecondition) {
      val freshPre = replace(argmap, freshenLocals(matchToIfThenElse(call.fi.funDef.precondition.get)))
      Implies(freshPre, tempExpr)
    } else {
      tempExpr
    }
    //flatten functions
    //TODO: should we freshen locals here ??
    ExpressionTransformer.normalizeExpr(template)
  }
  
  //axiomatic specification     
  protected var axiomRoots = Map[Seq[Call],Variable]() //a mapping from axioms keys (a sequence of calls) to the guards  
  def instantiateAxioms(formula: Formula, calls: Set[Call]) = {
    
    val debugSolver = if (this.debugAxiomInstantiation) {
      val sol = new UIFZ3Solver(ctx, program)
      sol.assertCnstr(formula.toExpr)
      Some(sol)
    } else None
    
    val inst1 = instantiateUnaryAxioms(formula,calls)
    val inst2 = instantiateBinaryAxioms(formula,calls)         
    val axiomInsts = inst1 ++ inst2                     
    
    Stats.updateCounterStats(Util.atomNum(And(axiomInsts)), "AxiomBlowup", "VC-refinement")
    ctx.reporter.info("Number of axiom instances: "+axiomInsts.size)

    if (this.debugAxiomInstantiation) {
      println("Instantianting axioms over: " + calls)
      println("Instantiated Axioms: ")
      axiomInsts.foreach((ainst) => {
        println(ainst)
        debugSolver.get.assertCnstr(ainst)
        val res = debugSolver.get.check
        res match {
          case Some(false) =>
            println("adding axiom made formula unsat!!")
          case _ => ;
        }
      })
      debugSolver.get.free
    }
  }
  
  //this code is similar to assuming specifications
  def instantiateUnaryAxioms(formula: Formula, calls: Set[Call]) = {
    val axioms = calls.collect {
      case call@_ if axiomFactory.hasUnaryAxiom(call) => {        
        val axiomInst = axiomFactory.unaryAxiom(call)

//        import ExpressionTransformer._
//        val nnfAxiom = pullAndOrs(TransformNot(axiomInst))
        val nnfAxiom = ExpressionTransformer.normalizeExpr(axiomInst)
        
        val cdata = formula.callData(call)
        formula.conjoinWithDisjunct(cdata.guard, nnfAxiom, cdata.parents)        
        axiomInst
      }
    }
    axioms.toSeq
  }
  
  /**
   * Here, we assume that axioms do not introduce calls. 
   * If this does not hold then 'guards' have to be used while instantiating axioms so as
   * to compute correct verification conditions. 
   * TODO: Use least common ancestor etc. to avoid axiomatizing calls along different disjuncts
   * TODO: can we avoid axioms like (a <= b ^ x<=y => p <= q), (x <= y ^ a<=b => p <= q), ...
   * TODO: can we have axiomatic specifications relating two different functions ?
   */
  protected var binaryAxiomCalls = Map[FunDef,Set[Call]]() //calls with axioms so far seen
  def getBinaxCalls(fd: FunDef) = if(binaryAxiomCalls.contains(fd)) binaryAxiomCalls(fd) else Set[Call]()
  def appendBinaxCalls(fd: FunDef, calls: Set[Call]) = {
    if (binaryAxiomCalls.contains(fd)) {
      val oldcalls = binaryAxiomCalls(fd)
      binaryAxiomCalls -= fd
      binaryAxiomCalls += (fd -> (oldcalls ++ calls))
    } else {
      binaryAxiomCalls += (fd -> calls)
    }
  }
  
  def instantiateBinaryAxioms(formula: Formula, calls: Set[Call]) = {

    val newCallsWithAxioms = calls.filter(axiomFactory.hasBinaryAxiom _)

    def isInstantiable(call1: Call, call2: Call): Boolean = {
      //important: check if the two calls refer to the same function      
      (call1.fi.funDef.id == call2.fi.funDef.id) && (call1 != call2)
    }
        
    def cross(a : Set[Call], b: Set[Call]) : Set[(Call,Call)] = {
      (for (x<-a; y<-b) yield (x,y)).filter(pair => isInstantiable(pair._1,pair._2))
    } 
      
    val product = cross(newCallsWithAxioms,getBinaxCalls(formula.fd)).flatMap(p => Seq((p._1,p._2),(p._2,p._1))) ++
      cross(newCallsWithAxioms,newCallsWithAxioms).map(p => (p._1,p._2))
             
    val axiomInsts = product.foldLeft(Seq[Expr]())((acc, pair) => {      
      val axiomInst = axiomFactory.binaryAxiom(pair._1, pair._2)
      
      //import ExpressionTransformer._
      //val nnfAxiom = pullAndOrs(TransformNot(axiomInst))
      val nnfAxiom = ExpressionTransformer.normalizeExpr(axiomInst)
            
      //union the parents of the two calls
      val parents = formula.callData(pair._1).parents ++ formula.callData(pair._2).parents       				
      val (axroot,_) = formula.conjoinWithRoot(nnfAxiom, parents)
      
      //important: here we need to update the axiom roots
      axiomRoots += (Seq(pair._1,pair._2) -> axroot)
      
      acc :+ axiomInst    
    })
    
    appendBinaxCalls(formula.fd, newCallsWithAxioms)
    axiomInsts
  }  
  
  /**
   * Note: taking a formula as input may not be necessary. We can store it as a part of the state
   * TODO: can we use transitivity here to optimize ?
   */
  def axiomsForCalls(formula: Formula, calls: Set[Call], model: Map[Identifier, Expr]): Seq[Constraint] = {  
    //note: unary axioms need not be instantiated     
    //consider only binary axioms
    (for (x<-calls; y<-calls) yield (x,y)).foldLeft(Seq[Constraint]())((acc, pair) => {      
      val (c1,c2) = pair
      if(c1 != c2){
        val axRoot = axiomRoots.get(Seq(c1,c2))
        if (axRoot.isDefined)
          acc ++ formula.pickSatDisjunct(axRoot.get, model)
        else acc        
      } else acc      
    })
  }
}
