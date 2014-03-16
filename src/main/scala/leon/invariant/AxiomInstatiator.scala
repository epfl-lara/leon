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
import leon.verification.ExtendedVC
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

class SpecInstantiator(ctx : LeonContext, program : Program, ctrTracker : ConstraintTracker) {               
    
  protected var exploredGuards = Set[Variable]() //the guards of the set of calls that were already processed
  def explored(guards: Set[Variable]) = {
    exploredGuards ++= guards
  }
  
  //normal specification
  
  
  //axiomatic specification
  protected val debugAxiomInstantiation = false  
  protected var callsWithAxioms = Set[Call]() //calls with axioms so far seen
  type AxiomKey = Seq[Call]
  protected var axiomRoots = Map[AxiomKey,Variable]() //a mapping from axioms keys (for now pairs of calls) to the guards

  def getUnexploredCalls(formula: Formula): Set[(Variable,Call)] = {    
    val disjuncts = formula.disjunctsInFormula
    val newguards = disjuncts.keySet.diff(exploredGuards)
    newguards.flatMap(g => disjuncts(g).collect { case c: Call => (g,c) })    
  }
   
  def instantiate() = {                 
    val funcs = ctrTracker.getFuncs        
    funcs.foreach((fd) => {
      val formula = ctrTracker.getVC(fd)                  
      val newEntries = getUnexploredCalls(formula)
      val newguards = newEntries.map(_._1)     
      
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
      
      instantiateAxioms(formula, newEntries)
      explored(newguards)
    })    
  }
  
  def instantiateAxioms(formula: Formula, callGuardPairs: Set[(Variable,Call)]) = {
    
    val debugSolver = if (SpecInstantiator.this.debugAxiomInstantiation) {
      val sol = new UIFZ3Solver(ctx, program)
      sol.assertCnstr(formula.toExpr)
      Some(sol)
    } else None
    
    val (cd1, inst1) = instantiateUnaryAxioms(formula,callGuardPairs)
    val (cd2, inst2) = instantiateBinaryAxioms(formula,callGuardPairs.map(_._2))
        
    callsWithAxioms ++= (cd1 ++ cd2)     
    val axiomInsts = inst1 ++ inst2 //this is a disjoint union as keys are different for 'inst1' and 'inst2'                    
    
    Stats.updateCounterStats(InvariantUtil.atomNum(And(axiomInsts)), "AxiomBlowup", "VC-refinement")
    ctx.reporter.info("Number of axiom instances: "+axiomInsts.size)

    if (SpecInstantiator.this.debugAxiomInstantiation) {
      println("Instantianting axioms over: " + (cd1 ++ cd2))
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
  
  def instantiateUnaryAxioms(formula: Formula, callGuardPairs: Set[(Variable,Call)]) : (Set[Call], Seq[Expr]) = {
    val callToAxioms = callGuardPairs.collect {
      case (g, call) if hasUnaryAxiom(call)) => {
        val axiomInst = unaryAxiom(call)

        import ExpressionTransformer._
        val nnfAxiom = pullAndOrs(TransformNot(axiomInst))
        val (_, (_, _) = formula.conjoinWithDisjunct(g, nnfAxiom) match(_, _) = formula.conjoinWithDisjunct(g, nnfAxiom)
        //note: we need not update axiom roots here.
        (call, axiomInst)
      }
    }.toMap
    (callToAxioms.keySet, callToAxioms.values.toSeq)
  }
  
  /**
   * Here, we assume that axioms do not introduce calls. 
   * If this does not hold then 'guards' have to be used while instantiating axioms so as
   * to compute correct verification conditions. 
   * TODO: Use least common ancestor etc. to avoid axiomatizing calls along different disjuncts
   * TODO: can we avoid axioms like (a <= b ^ x<=y => p <= q), (x <= y ^ a<=b => p <= q), ...
   */
  def instantiateBinaryAxioms(formula: Formula, calls: Set[Call]) = {

    val newCallsWithAxioms = calls.filter(hasBinaryAxiom _)

    def isInstantiable(call1: Call, call2: Call): Boolean = {
      //important: check if the two calls refer to the same function      
      (call1.fi.funDef.id == call2.fi.funDef.id) && (call1 != call2)
    }
        
    def cross(a : Set[Call], b: Set[Call]) : Set[(Call,Call)] = {
      (for (x<-a; y<-b) yield (x,y)).filter(pair => isInstantiable(pair._1,pair._2))
    } 
      
    val product = cross(newCallsWithAxioms,callsWithAxioms).flatMap(p => Seq((p._1,p._2),(p._2,p._1))) ++
      cross(newCallsWithAxioms,newCallsWithAxioms).map(p => (p._1,p._2))
             
    val axiomInsts = product.foldLeft(Seq[Expr]())((acc, pair) => {      
      val axiomInst = binaryAxiom(pair._1, pair._2)
      
      import ExpressionTransformer._
      val nnfAxiom = pullAndOrs(TransformNot(axiomInst))      
      val (axroot,_) = formula.conjoinWithRoot(nnfAxiom)
      axiomRoots += (Seq(pair._1,pair._2) -> axroot)
      
      acc :+ axiomInst    
    })
    
    (newCallsWithAxioms, axiomInsts)
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
  
  //Add more axioms here, if necessary
  var commuCalls = Set[Call]()
  def hasUnaryAxiom(call: Call) : Boolean = {
    //important: here we need to avoid applying commutativity on the calls produced by axioms instantiation
    (FunctionInfoFactory.isCommutative(call.fi.funDef) && !commuCalls.contains(call)) 
  }
  
  def hasBinaryAxiom(call: Call) : Boolean = {
	FunctionInfoFactory.isMonotonic(call.fi.funDef)   
  }
  
  def unaryAxiom(call: Call) : Expr = {
    val callee = call.fi.funDef
    if(FunctionInfoFactory.isCommutative(callee)) {
      //note: commutativity is defined only for binary operations
      val Seq(a1, a2) = call.fi.args
      val newret = TVarFactory.createTemp("cm").toVariable
      val newfi = FunctionInvocation(callee,Seq(a2,a1))
      val newcall = Equals(newret,newfi)
      
      commuCalls += Call(newret, newfi)
      
      And(newcall, Equals(newret, call.retexpr))
    } else 
      throw IllegalStateException("Call does not have unary axiom: "+call)
  }
  
  def binaryAxiom(call1: Call, call2: Call) : Expr = {    
    
    if(call1.fi.funDef.id != call2.fi.funDef.id) 
      throw IllegalStateException("Instantiating binary axiom on calls to different functions: "+call1+","+call2)
    
    val callee = call1.fi.funDef
    if(FunctionInfoFactory.isMonotonic(callee)) {
      monotonizeCalls(call1,call2)      
    } else 
      throw IllegalStateException("Call does not have binary axiom: "+call1)
  }
  
  def monotonizeCalls(call1: Call, call2: Call): Expr = {    
    val ant = (call1.fi.args zip call2.fi.args).foldLeft(Seq[Expr]())((acc, pair) => {
      val lesse = LessEquals(pair._1, pair._2)
      lesse +: alesse +: acc
    })
    val conseq = LessEquals(call1.retexpr, call2.retexpr)
    Implies(And(ant), conseq)    
  }
   
  //TODO: add distributivity axiom
}

//a set of functions for which we can assume templates
  private var useTemplates = Set[FunDef]()
  
  //a set of calls for which templates or specifications have not been assumed
  private var untemplatedCalls = Set[Call]()  
  private var unspecdCalls = Set[Call]()
  
  def initialize() : Unit = {
    
    //we can use templates for all the functions in the ctrTracker
    useTemplates ++= ctrTracker.getFuncs
       
    //initialize all heads
    headCalls = findNewHeads        
    
    //for debugging
    //println("Head-Calls: "+headCallPtrs.keys.toSeq)
    //System.exit(0)
    
    //This procedure has side-effects on many fields.   
    assumeSpecifications(headCalls)
  }

  //this has a side-effect on 'exploredGuards'
  private def findNewHeads: Set[Call] = {
    ctrTracker.getFuncs.flatMap((fd) => {
      val formula = ctrTracker.getVC(fd)
      val newguards = formula.disjunctsInFormula.keySet.diff(exploredGuards)
      val newheads = findHeads(formula, newguards.toSeq, List(fd))
      exploredGuards ++= newguards
      newheads
    }).toSet
  }

  /**
   * Heads are procedure calls whose target definitions have not been inlined.
   * The argument 'parents' represents the functions in the chain of unrolls that resulted in the 'ctrTree'  node.
   * This procedure has side-effects on 'callDataMap'
   */
  private def findHeads(formula: Formula, guards: Seq[Variable], parents: List[FunDef]): Set[Call] = {
    val disjuncts = formula.disjunctsInFormula
    guards.flatMap(g => {
      val calls = disjuncts(g).collect { case c: Call => c }
      calls.foreach((call) => {
        callDataMap += (call -> new CallData(formula, g, parents))
      })
      calls
    }).toSet
  }    

  /**
   * This procedure refines the existing abstraction.
   * Currently, the refinement happens by unrolling the head functions.   
   */
  def refineAbstraction(toRefineCalls : Option[Set[Call]]): Set[Call] = {
    
    //collect all new heads
    var newheads = findNewHeads
    headCalls ++= newheads
    
    //unroll each call in the head pointers (and in toRefineCalls)
    val callsToProcess = if(toRefineCalls.isDefined){
      
      //pick only those calls that have been least unrolled      
      val relevCalls = headCalls.intersect(toRefineCalls.get)      
      //minCalls are calls that have been least unrolled
      var minCalls = Set[Call]()
      var minUnrollings = MAX_UNROLLS
      relevCalls.foreach((call) => {
        val calldata = callDataMap(call)            
        val occurrences  = calldata.parents.count(_ == call.fi.funDef)
        if(occurrences < minUnrollings) {
          minUnrollings = occurrences
          minCalls = Set(call)
        }
        else if(occurrences == minUnrollings) {
          minCalls += call
        }        
      })
      minCalls
      
    } else headCalls
    
    println("Unrolling: "+ callsToProcess.size+"/"+headCalls.size)
    //println("Unrolled calls: "+callsToProcess.map(_.expr))
    
    val unrolls = callsToProcess.foldLeft(Set[Call]())((acc, call) => {      

      val calldata = callDataMap(call)            
      val occurrences  = calldata.parents.count(_ == call.fi.funDef)
      //if the call is not a recursive call, unroll it unconditionally      
      if(occurrences == 0) {
        newheads ++= unrollCall(call, calldata)
        acc + call
      } else {
    	 //if the call is recursive, unroll iff the number of times the recursive function occurs in the context is < MAX-UNROLL        
        if(occurrences < MAX_UNROLLS)
        {
          newheads ++= unrollCall(call, calldata)
          acc + call
        } else{
          //otherwise, drop the call. Here we are not unrolling the call
          acc 
        }         
      }
      //TODO: are there better ways of unrolling ??      
    })
    
    //update the head functions 
    headCalls = headCalls.diff(callsToProcess) ++ newheads

    if (!unrolls.isEmpty) {
      //assume the post-conditions for the newcalls in the VCs
      assumeSpecifications(newheads)
    }    
    unrolls
  }


  /**
   * This function refines the constraint tree by assuming the specifications/templates for calls in
   * the formula
   * Here, assume (pre => post ^ template)
   * Important: adding templates for unspecdCalls of the previous iterations is empirically more effective
   */
  def assumeSpecifications(newheads : Set[Call]): Set[Call] = {    
    //initialized unspecd calls
    unspecdCalls ++= newheads   
    
    var foundheads = Set[Call]()    
    //assume specifications    
    unspecdCalls.foreach((call) => {
      //first get the spec for the call if it exists 
      val spec = specForCall(call)
      if (spec.isDefined && spec.get != tru) {
    	val cdata = callDataMap(call)
        val (_, newguards) = cdata.formula.conjoinWithDisjunct(cdata.guard, spec.get)        
        foundheads ++= findHeads(cdata.formula, newguards, cdata.parents)
      }
    })

    //try to assume templates for all the current un-templated calls    
    var newUntemplatedCalls = Set[Call]()    
    untemplatedCalls.foreach((call) => {
      //first get the template for the call if one needs to be added
      if (useTemplates.contains(call.fi.funDef)) {
        val temp = templateForCall(call)
        val cdata = callDataMap(call)
        val (_, newguards) = cdata.formula.conjoinWithDisjunct(cdata.guard, temp)        
        foundheads ++= findHeads(cdata.formula, newguards, cdata.parents)
        
      } else {
        newUntemplatedCalls += call
      }
    })
    untemplatedCalls = newUntemplatedCalls    
    
    //add unspecd calls to untemplatedcalls
    untemplatedCalls ++= unspecdCalls
    //update unspecd calls
    unspecdCalls = foundheads
    foundheads
  }

  def specForCall(call: Call): Option[Expr] = {
    val argmap = InvariantUtil.formalToAcutal(call)
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
    val argmap = InvariantUtil.formalToAcutal(call)
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
