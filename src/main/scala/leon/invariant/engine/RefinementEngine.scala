/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.engine

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.TypeOps.instantiateType
import purescala.Extractors._
import purescala.Types._
import java.io._

import invariant.templateSolvers._
import invariant.factories._
import invariant.util._
import invariant.util.Util._
import invariant.structure._
import FunctionUtils._
import Util._
import PredicateUtil._
import ProgramUtil._

//TODO: the parts of the code that collect the new head functions is ugly and has many side-effects. Fix this.
//TODO: there is a better way to compute heads, which is to consider all guards not previous seen
class RefinementEngine(ctx: InferenceContext, prog: Program, ctrTracker: ConstraintTracker) {

  val tru = BooleanLiteral(true)
  val reporter = ctx.reporter
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

      val newheads = formula.getCallsOfGuards(newguards.toSeq) //.flatMap(g => disjuncts(g).collect { case c: Call => c })
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
        //TODO: are there better ways of unrolling ?? Yes. Akask Lal "dag Inlining". Implement that!
      })

      //update the head functions
      resetHeads(fd, allheads.diff(callsToProcess))
      unrolls
    }).toSet
  }
  import leon.transformations.InstUtil._

  def shouldCreateVC(recFun: FunDef, inSpec: Boolean): Boolean = {
    if (ctrTracker.hasVC(recFun)) false
    else {
      //need not create vcs for theory operations and library methods
      !recFun.isTheoryOperation && !recFun.annotations.contains("library") &&
        (recFun.template match {
          case Some(temp) if inSpec && isResourceBoundOf(recFun)(temp) => false // TODO: here we can also drop resource templates if it is used with other templates
          case Some(_) => true
          case _ => false
        })
    }
  }

  /**
   * Returns a set of unrolled calls and a set of new head functions
   * here we unroll the methods in the current abstraction by one step.
   * This procedure has side-effects on 'headCalls' and 'callDataMap'
   */
  def unrollCall(call: Call, formula: Formula) {
    val fi = call.fi
    val calldata = formula.callData(call)
    val callee = fi.tfd.fd
    if (fi.tfd.fd.hasBody) {
      //freshen the body and the post
      val isRecursive = cg.isRecursive(callee)
      if (isRecursive) {
        val recFun = callee
        val recFunTyped = fi.tfd
        //check if we need to create a VC formula for the call's target
        if (shouldCreateVC(recFun, calldata.inSpec)) {
          reporter.info("Creating VC for " + recFun.id)
          // instantiate the body with new types
          val tparamMap = (recFun.typeArgs zip recFunTyped.tps).toMap
          val paramMap = recFun.params.map { pdef =>
            pdef.id -> FreshIdentifier(pdef.id.name, instantiateType(pdef.id.getType, tparamMap))
          }.toMap
          val freshBody = instantiateType(freshenLocals(recFun.body.get), tparamMap, paramMap)
          val resname = if (recFun.hasPostcondition) getResId(recFun).get.name else "res"
          //create a new result variable here for the same reason as freshening the locals,
          //which is to avoid variable capturing during unrolling
          val resvar = Variable(FreshIdentifier(resname, recFunTyped.returnType, true))
          val bodyExpr = Equals(resvar, freshBody)
          val pre = recFun.precondition.map(p => instantiateType(p, tparamMap, paramMap)).getOrElse(tru)
          //note: here we are only adding the template as the postcondition (other post need not be proved again)
          val idmap = formalToActual(Call(resvar, FunctionInvocation(recFunTyped, paramMap.values.toSeq.map(_.toVariable))))
          val postTemp = replace(idmap, recFun.getTemplate)
          //val vcExpr = ExpressionTransformer.normalizeExpr(And(bodyExpr, Not(postTemp)), ctx.multOp)
          ctrTracker.addVC(recFun, pre, bodyExpr, postTemp)
        }
        //Here, unroll the call into the caller tree
        if (verbose) reporter.info("Unrolling " + Equals(call.retexpr, call.fi))
        inilineCall(call, calldata, formula)
      } else {
        //here we are unrolling a function without template
        if (verbose) reporter.info("Unfolding " + Equals(call.retexpr, call.fi))
        inilineCall(call, calldata, formula)
      }
    } else Set()
  }

  def inilineCall(call: Call, calldata: CallData, formula: Formula) {
    val tfd = call.fi.tfd
    val callee = tfd.fd
    if (callee.isBodyVisible) {
      //here inline the body and conjoin it with the guard
      //Important: make sure we use a fresh body expression here, and freshenlocals
      val tparamMap = (callee.typeArgs zip tfd.tps).toMap
      val freshBody = instantiateType(replace(formalToActual(call),
        Equals(getFunctionReturnVariable(callee), freshenLocals(callee.body.get))),
        tparamMap, Map())
      val inlinedSummary = ExpressionTransformer.normalizeExpr(freshBody, ctx.multOp)
      if (this.dumpInlinedSummary)
        println(s"Call: ${call} \n FunDef: $callee \n Inlined Summary of ${callee.id}: $inlinedSummary")
      //conjoin the summary with the disjunct corresponding to the 'guard'
      //note: the parents of the summary are the parents of the call plus the callee function
      formula.conjoinWithDisjunct(calldata.guard, inlinedSummary, (callee +: calldata.parents), calldata.inSpec)
    } else {
      if (verbose)
        reporter.info(s"Not inlining ${call.fi}: body invisible!")
    }
  }
}
