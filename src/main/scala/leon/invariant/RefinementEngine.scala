package leon
package invariant

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
import leon.evaluators._
import java.io._
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
import leon.invariant._
import leon.purescala.ScalaPrinter

/**
 * Note: the formula and the guard are used to locate the disjunct for unrolling the call
 */
class CallData(val formula: Formula, val guard : Variable, val parents: List[FunDef]) {  
}

//TODO: the parts of the code that collect the new head functions is ugly and has many side-effects. Fix this.
//TODO: there is a better way to compute heads, which is to consider all guards not previous seen
class RefinementEngine(ctx: LeonContext, prog: Program, ctrTracker: ConstraintTracker, tempFactory : TemplateFactory) {
    
  val tru = BooleanLiteral(true)
  val reporter = ctx.reporter
  
  //this count indicates the number of times we unroll a recursive call
  private val MAX_UNROLLS = 2
  
  //debugging flags
  private val dumpInlinedSummary = false
  
  //a mapping from a call to the node containing the call (plus some additional data like the list of transitive callers etc.)
  private var callDataMap = Map[Call, CallData]()
  
  //a set of calls that have not been unrolled (these are potential unroll candidates)
  //However, these calls except those given by the unspecdCalls have been specified
  private var headCalls = Set[Call]()

  //the guards of disjuncts that were already processed
  private var exploredGuards = Set[Variable]()
  
  //a set of functions for which we can assume templates
  private var useTemplates = Set[FunDef]()
  
  //a set of calls for which templates or specifications have not been assumed
  private var untemplatedCalls = Set[Call]()  
  private var unspecdCalls = Set[Call]()
  
  def initialize() : Unit = {
    
    //we can use templates for all the functions in the ctrTracker
    useTemplates ++= ctrTracker.getFuncs
    
    headCalls = findAllHeads
    
    //for debugging
    //println("Head-Calls: "+headCallPtrs.keys.toSeq)
    //System.exit(0)
    
    //This procedure has side-effects on many fields.   
    headCalls ++= assumeSpecifications(headCalls)
  }

  private def findAllHeads: Set[Call] = {
    ctrTracker.getFuncs.flatMap((fd) => {
      val formula = ctrTracker.getVC(fd)
      findHeads(formula, formula.disjunctsInFormula.keys.toSeq, List(fd))
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
    var newheads = Set[Call]()    
    
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
      //assume the post-conditions for the calls in the VCs
      headCalls ++= assumeSpecifications(newheads)
    }    
    unrolls
  }
  
  def shouldCreateVC(recFun: FunDef) : Boolean = {
    if(ctrTracker.hasVC(recFun)) false
    else {
      //need not create trees for theory operations
      if(FunctionInfoFactory.isTheoryOperation(recFun)) {
        false
      } else {
        true 
      }          
    }
  }

  /**
   * Returns a set of unrolled calls and a set of new head functions   
   * here we unroll the methods in the current abstraction by one step.
   * This procedure has side-effects on 'headCalls' and 'callDataMap'
   */   
  def unrollCall(call : Call, calldata : CallData): Set[Call] = {                

    //println("Processing: "+call)
    val fi = call.fi
    if (fi.funDef.hasBody) {

      //freshen the body and the post           
      val isRecursive = prog.isRecursive(fi.funDef)        
      if(isRecursive) {                        
        var newheads = Set[Call]()
        val recFun = fi.funDef
                
        //check if we need to create a constraint tree for the call's target
        if (shouldCreateVC(recFun)) {
          useTemplates += recFun
          //create a new verification condition for this recursive function          
          println("Creating VC for "+fi.funDef.id)
          val freshBody = freshenLocals(matchToIfThenElse(recFun.nondetBody.get))
          val resvar = if (recFun.hasPostcondition) {
            //create a new result variable here for the same reason as freshening the locals,
            //which is to avoid variable capturing during unrolling            
            val origRes = recFun.postcondition.get._1
            Variable(FreshIdentifier(origRes.name, true).setType(origRes.getType))            
          } else {
            //create a new resvar
            Variable(FreshIdentifier("res", true).setType(recFun.returnType))
          }          
          val plainBody = Equals(resvar,freshBody)
          val bodyExpr = if (recFun.hasPrecondition) {
            And(matchToIfThenElse(recFun.precondition.get), plainBody)
          } else plainBody
                    
          val idmap = InvariantUtil.formalToAcutal(Call(resvar, FunctionInvocation(recFun, recFun.args.map(_.toVariable))))
          val postTemp = tempFactory.constructTemplate(idmap, recFun)
          val vcExpr =  ExpressionTransformer.normalizeExpr(And(bodyExpr,Not(postTemp)))
          ctrTracker.addVC(recFun, vcExpr)
          //val npostTemp = ExpressionTransformer.normalizeExpr(Not(postTemp))

          //Find new heads
          val formula = ctrTracker.getVC(recFun)
          newheads ++= findHeads(formula, formula.disjunctsInFormula.keys.toSeq, List(recFun))           
        }        
                   
        //Here, unroll the call into the caller tree
        println("Unrolling " + Equals(call.retexpr,call.fi))
        newheads ++= inilineCall(call, calldata.formula, calldata.guard, calldata.parents)          
        newheads
      }
      else {        
        //here we are unrolling a non-recursive function
        println("Inlining "+Equals(call.retexpr,call.fi))               
        inilineCall(call, calldata.formula, calldata.guard, calldata.parents)        
      }                
    } else Set()    
  }

  /**
  * The parameter 'resVar' is the result variable of the body
  **/
  def inilineCall(call : Call, formula: Formula, guard: Variable, parents : List[FunDef]) : Set[Call] = {    
    //here inline the body and conjoin it with the guard
    val callee = call.fi.funDef   
    
    //Important: make sure we use a fresh body expression here    
    val freshBody = freshenLocals(matchToIfThenElse(callee.nondetBody.get))
    val calleeSummary = 
      Equals(InvariantUtil.getFunctionReturnVariable(callee), freshBody)       
    val argmap1 = InvariantUtil.formalToAcutal(call)
    val inlinedSummary = ExpressionTransformer.normalizeExpr(replace(argmap1, calleeSummary))
    
    if(this.dumpInlinedSummary)
    	println("Inlined Summary: "+inlinedSummary)

    //conjoin the summary with the disjunct corresponding to the 'guard'
    val (_, newguards) = formula.conjoinWithDisjunct(guard, inlinedSummary) 
              
    //Find new heads     
    val newheads = findHeads(formula, newguards, (callee +: parents))
    newheads
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
}
