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
import leon.verification.Tactic
import leon.verification.VerificationReport
import leon.invariant._
import leon.purescala.ScalaPrinter

//TODO: the parts of the code that collect the new head functions is ugly and has many side-effects. Fix this.
//TODO: there is a better way to compute heads, which is to consider all guards not previous seen
class RefinementEngine(ctx: LeonContext, prog: Program, ctrTracker: ConstraintTracker, tempFactory : TemplateFactory) {
    
  val tru = BooleanLiteral(true)
  val reporter = ctx.reporter
  
  //this count indicates the number of times we unroll a recursive call
  private val MAX_UNROLLS = 2
  
  //debugging flags
  private val dumpInlinedSummary = false
  
  //the guards of disjuncts that were already processed
  private var exploredGuards = Set[Variable]()
  
  //a set of calls that have not been unrolled (these are potential unroll candidates)
  //However, these calls except those given by the unspecdCalls have been assumed specifications
  private var headCalls = Map[FunDef,Set[Call]]()  
  def getHeads(fd: FunDef) =  if(headCalls.contains(fd)) headCalls(fd) else Set()
  def resetHeads(fd: FunDef, heads: Set[Call]) = {
    if (headCalls.contains(fd)) {
      headCalls -= fd
      headCalls += (fd -> heads)
    } else {
      headCalls += (fd -> heads)
    }
  }

  /**
   * This procedure refines the existing abstraction.
   * Currently, the refinement happens by unrolling the head functions.
   */
  def refineAbstraction(toRefineCalls: Option[Set[Call]]): Set[Call] = {

    ctrTracker.getFuncs.flatMap((fd) => {
      val formula = ctrTracker.getVC(fd)
      val disjuncts = formula.disjunctsInFormula
      val newguards = formula.disjunctsInFormula.keySet.diff(exploredGuards)
      exploredGuards ++= newguards

      val newheads = newguards.flatMap(g => disjuncts(g).collect { case c: Call => c })
      val allheads = getHeads(fd) ++ newheads      				 

      //unroll each call in the head pointers and in toRefineCalls
      val callsToProcess = if (toRefineCalls.isDefined) {

        //pick only those calls that have been least unrolled      
        val relevCalls = allheads.intersect(toRefineCalls.get)
        var minCalls = Set[Call]()
        var minUnrollings = MAX_UNROLLS
        relevCalls.foreach((call) => {
          val calldata = formula.callData(call)
          val recInvokes = calldata.parents.count(_ == call.fi.funDef)
          if (recInvokes < minUnrollings) {
            minUnrollings = recInvokes
            minCalls = Set(call)
          } else if (recInvokes == minUnrollings) {
            minCalls += call
          }
        })
        minCalls

      } else allheads

      println("Unrolling: " + callsToProcess.size + "/" + allheads.size)
      //println("Unrolled calls: "+callsToProcess.map(_.expr))

      val unrolls = callsToProcess.foldLeft(Set[Call]())((acc, call) => {

        val calldata = formula.callData(call)
        val recInvokes = calldata.parents.count(_ == call.fi.funDef)
        //if the call is not a recursive call, unroll it unconditionally      
        if (recInvokes == 0) {
          unrollCall(call, formula)
          acc + call
        } else {
          //if the call is recursive, unroll iff the number of times the recursive function occurs in the context is < MAX-UNROLL        
          if (recInvokes < MAX_UNROLLS) {
            unrollCall(call, formula)
            acc + call
          } else {
            //otherwise, do not unroll the call
            acc
          }
        }
        //TODO: are there better ways of unrolling ??      
      })

      //update the head functions 
      resetHeads(fd, allheads.diff(callsToProcess))
      unrolls
    }).toSet
  }

  def shouldCreateVC(recFun: FunDef) : Boolean = {
    if(ctrTracker.hasVC(recFun)) false
    else {
      //need not create trees for theory operations
      val funinfo = FunctionInfoFactory.getFunctionInfo(recFun)
      if(funinfo.isDefined && funinfo.get.isTheoryOp) {
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
  def unrollCall(call : Call, formula: Formula) = {                

    //println("Processing: "+call)
    val fi = call.fi
    if (fi.funDef.hasBody) {

      //freshen the body and the post           
      val isRecursive = prog.isRecursive(fi.funDef)        
      if(isRecursive) {                               
        val recFun = fi.funDef
                
        //check if we need to create a constraint tree for the call's target
        if (shouldCreateVC(recFun)) {
          
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
                    
          //note: here we are only adding the template as the postcondition
          val idmap = Util.formalToAcutal(Call(resvar, FunctionInvocation(recFun, recFun.args.map(_.toVariable))))
          val postTemp = tempFactory.constructTemplate(idmap, recFun)
          val vcExpr =  ExpressionTransformer.normalizeExpr(And(bodyExpr,Not(postTemp)))
          ctrTracker.addVC(recFun, vcExpr)
        }        
                   
        //Here, unroll the call into the caller tree
        println("Unrolling " + Equals(call.retexpr,call.fi))
        inilineCall(call, formula)                  
      }
      else {        
        //here we are unrolling a non-recursive function
        println("Inlining "+Equals(call.retexpr,call.fi))               
        inilineCall(call, formula)        
      }                
    } else Set()    
  }

  
  def inilineCall(call : Call, formula: Formula) = {    
    //here inline the body and conjoin it with the guard
    val callee = call.fi.funDef   
    
    //Important: make sure we use a fresh body expression here    
    val freshBody = freshenLocals(matchToIfThenElse(callee.nondetBody.get))
    val calleeSummary = 
      Equals(Util.getFunctionReturnVariable(callee), freshBody)       
    val argmap1 = Util.formalToAcutal(call)
    val inlinedSummary = ExpressionTransformer.normalizeExpr(replace(argmap1, calleeSummary))
    
    if(this.dumpInlinedSummary)
    	println("Inlined Summary: "+inlinedSummary)

    //conjoin the summary with the disjunct corresponding to the 'guard'
    //note: the parents of the summary are the parents of the call plus the callee function
    val calldata = formula.callData(call)
    formula.conjoinWithDisjunct(calldata.guard, inlinedSummary, (callee +: calldata.parents))                   
  }
}
