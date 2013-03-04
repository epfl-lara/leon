package leon
package invariant.engine
import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import java.io._
import solvers.z3.UIFZ3Solver
import invariant._
import scala.util.control.Breaks._
import solvers._
import scala.concurrent._
import scala.concurrent.duration._

import invariant.templateSolvers._
import invariant.factories._
import invariant.util._
import invariant.structure._

class SpecInstantiator(ctx : InferenceContext, ctrTracker : ConstraintTracker, tempFactory : TemplateFactory) {               
    
  protected val disableAxioms = false
  protected val debugAxiomInstantiation = false  
  
  val tru = BooleanLiteral(true)
  val axiomFactory = new AxiomFactory(ctx) //handles instantiation of axiomatic specification
  val program = ctx.program
  
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
      if (!disableAxioms) {
        //remove all multiplication if "withmult" is specified
        val relavantCalls = if (ctx.withmult) {          
          newcalls.filter(call => (call.fi.tfd.fd != ctx.pivmultfun) && (call.fi.tfd.fd != ctx.multfun))
        }else newcalls        
        instantiateAxioms(formula, relavantCalls)
      }    	 
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
      if (funcsWithVC.contains(call.fi.tfd.fd)) {
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
    val callee = call.fi.tfd.fd
    if (callee.hasPostcondition) {
      val (resvar, post) = callee.postcondition.get
      val freshPost = freshenLocals(matchToIfThenElse(post))

      val spec = if (callee.hasPrecondition) {
        val freshPre = freshenLocals(matchToIfThenElse(callee.precondition.get))
        Implies(freshPre, freshPost)
      } else {
        freshPost
      }
      val inlinedSpec = ExpressionTransformer.normalizeExpr(replace(argmap, spec),ctx.multOp)
      Some(inlinedSpec)
    } else {
      None
    }
  }

  def templateForCall(call: Call): Expr = {
    val argmap = Util.formalToAcutal(call)
    val callee = call.fi.tfd.fd
    val tempExpr = tempFactory.constructTemplate(argmap, callee)
    val template = if (callee.hasPrecondition) {
      val freshPre = replace(argmap, freshenLocals(matchToIfThenElse(callee.precondition.get)))
      Implies(freshPre, tempExpr)
    } else {
      tempExpr
    }
    //flatten functions
    //TODO: should we freshen locals here ??
    ExpressionTransformer.normalizeExpr(template, ctx.multOp)
  }
  
  //axiomatic specification     
  protected var axiomRoots = Map[Seq[Call],Variable]() //a mapping from axioms keys (a sequence of calls) to the guards  
  def instantiateAxioms(formula: Formula, calls: Set[Call]) = {
    
    val debugSolver = if (this.debugAxiomInstantiation) {
      val sol = new UIFZ3Solver(ctx.leonContext, program)
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
        val (ant,conseq) = axiomFactory.unaryAxiom(call)
        val axiomInst = Implies(ant,conseq)

//        import ExpressionTransformer._
//        val nnfAxiom = pullAndOrs(TransformNot(axiomInst))       
        val nnfAxiom = ExpressionTransformer.normalizeExpr(axiomInst, ctx.multOp)
        
        val cdata = formula.callData(call)
        formula.conjoinWithDisjunct(cdata.guard, nnfAxiom, cdata.parents)        
        axiomInst
      }
    }
    axioms.toSeq
  }
  
  /**
   * Here, we assume that axioms do not introduce calls. 
   * If this does not hold, 'guards' have to be used while instantiating axioms so as
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
      (call1.fi.tfd.id == call2.fi.tfd.id) && (call1 != call2)
    }           
      
    val product = Util.cross[Call,Call](newCallsWithAxioms,getBinaxCalls(formula.fd),Some(isInstantiable)).flatMap(
        p => Seq((p._1,p._2),(p._2,p._1))) ++ 
        Util.cross[Call,Call](newCallsWithAxioms,newCallsWithAxioms,Some(isInstantiable)).map(p => (p._1,p._2))
             
    ctx.reporter.info("# of pairs with axioms: "+product.size)
    //Stats.updateCumStats(product.size, "Call-pairs-with-axioms")

    val addedAxioms = product.flatMap(pair => {
      //union the parents of the two calls
      val cdata1 = formula.callData(pair._1)
      val cdata2 = formula.callData(pair._2)
      val parents = cdata1.parents ++ cdata2.parents
      val axiomInsts = axiomFactory.binaryAxiom(pair._1, pair._2)

      axiomInsts.foldLeft(Seq[Expr]())((acc, inst) => {
        val (ant, conseq) = inst
        val axiom = Implies(ant, conseq)
        val nnfAxiom = ExpressionTransformer.normalizeExpr(axiom, ctx.multOp)
        val (axroot, _) = formula.conjoinWithRoot(nnfAxiom, parents)
        //important: here we need to update the axiom roots
        axiomRoots += (Seq(pair._1, pair._2) -> axroot)
        acc :+ axiom
      })
    })                
    appendBinaxCalls(formula.fd, newCallsWithAxioms)
    addedAxioms
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

/**
 * Some unused code
 * 
    //collect variables that depend on the inputs
    val indepVars = formula.independentVars
    ctx.reporter.info("Indep. vars: "+indepVars.size+"/"+variablesOf(formula.toExpr).size)    
    val nonparamSolver = new UIFZ3Solver(this.ctx, this.program)
    val paramFormula = formula.splitParamPart._2
    nonparamSolver.assertCnstr(paramFormula)
    //println("Param Formula: "+paramFormula)

    /**
     * Returns 'true' if the axiomPre is implied by the Formula
     * 'false' if axiomPre is not implied by the Formula
     * 'None' if axiomPre could be implied by the Formula depending on the assignment for parameters
     * TODO: should we try and eliminate those that are related by template variables ?
     */
    def impliedByGuards(guards: Seq[Variable],axiomPre: Expr): Option[Boolean] = {
      if (!variablesOf(axiomPre).diff(indepVars).isEmpty) {
        //here, the axiom may depend on non-input variables. So we cannot decide        
        None
      } else {
        //here the axiomPre consists of only independent variables        
        nonparamSolver.push
        nonparamSolver.assertCnstr(Implies(And(guards), Not(axiomPre)))
        val res = nonparamSolver.check match {
          case Some(false) => {
            //here the axiomPre is implied          
            //println("Implied: "+Implies(And(guards), axiomPre))            
            Some(true)
          }
          case Some(true) => {
            //here we can for sure say that the axiom will not be implied by any assignment of values to template variables
        	//TODO: this does not hold if we start considering templates with disjunctions in the postcondition
            //println("Not implied: "+Implies(And(guards), axiomPre))
            Some(false)
          }
          case None => None
        }
        nonparamSolver.pop()
        res
      }
    }
    var droppedAxioms = 0
    val addedAxioms = product.flatMap(pair => {
      //union the parents of the two calls
      val cdata1 = formula.callData(pair._1)
      val cdata2 = formula.callData(pair._2)
      val parents = cdata1.parents ++ cdata2.parents
      val guards = Seq(cdata1.guard, cdata2.guard)
      val axiomInsts = axiomFactory.binaryAxiom(pair._1, pair._2)

      //select axioms based on whether the axiom ant could be implied by the formula      
      axiomInsts.foldLeft(Seq[Expr]())((acc, inst) => {
        val (ant, conseq) = inst
        val implied = impliedByGuards(guards, ant)
        implied match {
          case Some(true) => {
            //add the consequence alone to the root
            //TODO: should we use the guard here ??            
            formula.conjoinWithRoot(ExpressionTransformer.normalizeExpr(conseq), parents)
            acc :+ conseq
          }
          case None => {            
            val axiom = Implies(ant, conseq)
            val nnfAxiom = ExpressionTransformer.normalizeExpr(axiom)
            val (axroot, _) = formula.conjoinWithRoot(nnfAxiom, parents)
            //important: here we need to update the axiom roots
            axiomRoots += (Seq(pair._1, pair._2) -> axroot)
            acc :+ axiom
          }
          case _ => {
            droppedAxioms += 1
            acc //need not do anything if impliedByFormula(ant) is false                     
          }
        }
      })
    })        
    ctx.reporter.info("# of dropped axioms: "+droppedAxioms)
    Stats.updateCumStats(droppedAxioms, "dropped-axioms")
    
    //free the solver
    nonparamSolver.free
 */
