package leon
package invariant.engine

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._

import invariant.templateSolvers._
import invariant.factories._
import invariant.util._
import invariant.util.Util._
import invariant.structure._
import FunctionUtils._

//TODO: the parts of the code that collect the new head functions is ugly and has many side-effects. Fix this.
//TODO: there is a better way to compute heads, which is to consider all guards not previous seen
class RefinementEngine(ctx: InferenceContext, ctrTracker: ConstraintTracker) {

  val tru = BooleanLiteral(true)
  val reporter = ctx.reporter
  val prog = ctx.program
  val cg = CallGraphUtil.constructCallGraph(prog)

  //this count indicates the number of times we unroll a recursive call
  private val MAX_UNROLLS = 2

  //debugging flags
  private val dumpInlinedSummary = false

  //print flags
  val verbose = false

  //the guards of disjuncts that were already processed
  private var exploredGuards = Set[Variable]()

  //a set of calls that have not been unrolled (these are potential unroll candidates)
  //However, these calls except those given by the unspecdCalls have been assumed specifications
  private var headCalls = Map[FunDef, Set[Call]]()
  def getHeads(fd: FunDef) = if (headCalls.contains(fd)) headCalls(fd) else Set()
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
          val recInvokes = calldata.parents.count(_ == call.fi.tfd.fd)
          if (recInvokes < minUnrollings) {
            minUnrollings = recInvokes
            minCalls = Set(call)
          } else if (recInvokes == minUnrollings) {
            minCalls += call
          }
        })
        minCalls

      } else allheads

      if (verbose)
        reporter.info("Unrolling: " + callsToProcess.size + "/" + allheads.size)

      val unrolls = callsToProcess.foldLeft(Set[Call]())((acc, call) => {

        val calldata = formula.callData(call)
        val recInvokes = calldata.parents.count(_ == call.fi.tfd.fd)
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

  def shouldCreateVC(recFun: FunDef): Boolean = {
    if (ctrTracker.hasVC(recFun)) false
    else {
      //need not create vcs for theory operations
      !recFun.isTheoryOperation && recFun.hasTemplate &&
      	!recFun.annotations.contains("library")
    }
  }

  /**
   * Returns a set of unrolled calls and a set of new head functions
   * here we unroll the methods in the current abstraction by one step.
   * This procedure has side-effects on 'headCalls' and 'callDataMap'
   */
  def unrollCall(call: Call, formula: Formula) = {
    val fi = call.fi
    if (fi.tfd.fd.hasBody) {

      //freshen the body and the post
      val isRecursive = cg.isRecursive(fi.tfd.fd)
      if (isRecursive) {
        val recFun = fi.tfd.fd
        val recFunTyped = fi.tfd

        //check if we need to create a constraint tree for the call's target
        if (shouldCreateVC(recFun)) {

          //create a new verification condition for this recursive function
          reporter.info("Creating VC for " + recFun.id)
          val freshBody = freshenLocals(matchToIfThenElse(recFun.body.get))
          val resvar = if (recFun.hasPostcondition) {
            //create a new result variable here for the same reason as freshening the locals,
            //which is to avoid variable capturing during unrolling
            val origRes = getResId(recFun).get
            Variable(FreshIdentifier(origRes.name, origRes.getType, true))
          } else {
            //create a new resvar
            Variable(FreshIdentifier("res", recFun.returnType, true))
          }
          val plainBody = Equals(resvar, freshBody)
          val bodyExpr = if (recFun.hasPrecondition) {
            And(matchToIfThenElse(recFun.precondition.get), plainBody)
          } else plainBody

          //note: here we are only adding the template as the postcondition
          val idmap = Util.formalToActual(Call(resvar, FunctionInvocation(recFunTyped, recFun.params.map(_.toVariable))))
          val postTemp = replace(idmap, recFun.getTemplate)
          val vcExpr = ExpressionTransformer.normalizeExpr(And(bodyExpr, Not(postTemp)), ctx.multOp)
          ctrTracker.addVC(recFun, vcExpr)
        }

        //Here, unroll the call into the caller tree
        if (verbose) reporter.info("Unrolling " + Equals(call.retexpr, call.fi))
        inilineCall(call, formula)
      } else {
        //here we are unrolling a function without template
        if (verbose) reporter.info("Unfolding " + Equals(call.retexpr, call.fi))
        inilineCall(call, formula)
      }
    } else Set()
  }

  def inilineCall(call: Call, formula: Formula) = {
    //here inline the body and conjoin it with the guard
    val callee = call.fi.tfd.fd

    //Important: make sure we use a fresh body expression here
    val freshBody = freshenLocals(matchToIfThenElse(callee.body.get))
    val calleeSummary =
      Equals(Util.getFunctionReturnVariable(callee), freshBody)
    val argmap1 = Util.formalToActual(call)
    val inlinedSummary = ExpressionTransformer.normalizeExpr(replace(argmap1, calleeSummary), ctx.multOp)

    if (this.dumpInlinedSummary)
      println("Inlined Summary: " + inlinedSummary)

    //conjoin the summary with the disjunct corresponding to the 'guard'
    //note: the parents of the summary are the parents of the call plus the callee function
    val calldata = formula.callData(call)
    formula.conjoinWithDisjunct(calldata.guard, inlinedSummary, (callee +: calldata.parents))
  }
}
