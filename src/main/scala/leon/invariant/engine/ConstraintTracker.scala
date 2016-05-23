/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.engine

import purescala.Definitions._
import purescala.Expressions._
import invariant.structure._
import invariant.util.ExpressionTransformer._
import purescala.ExprOps._
import invariant.util.PredicateUtil._

object ConstraintTracker {
  val debugVC = false
}
class ConstraintTracker(ctx : InferenceContext, program: Program, rootFun : FunDef/*, temFactory: TemplateFactory*/) {

  import ConstraintTracker._
  //a mapping from functions to its VCs represented as a CNF formula
  protected var funcVCs = Map[FunDef,Formula]()

  val vcRefiner = new RefinementEngine(ctx, program, this)
  val specInstantiator = new SpecInstantiator(ctx, program, this)

  def getFuncs : Seq[FunDef] = funcVCs.keys.toSeq
  def hasVC(fdef: FunDef) = funcVCs.contains(fdef)
  def getVC(fd: FunDef) : Formula = funcVCs(fd)

  /**
   * @param body the body part of the VC that may possibly have instrumentation
   * @param assump is the additional assumptions e.g. pre and conseq
   * is the goal e.g. post
   * The VC constructed is assump ^ body ^ Not(conseq)
   */
  def addVC(fd: FunDef, assump: Expr, body: Expr, conseq: Expr) = {
    if(debugVC) {
      println(s"Init VC \n assumption: $assump \n body: $body \n conseq: $conseq")
    }
    val flatBody = normalizeExpr(body, ctx.multOp)
    val flatAssump = normalizeExpr(assump, ctx.multOp)
    val conseqNeg = normalizeExpr(Not(conseq), ctx.multOp)
    val callCollect = collect {
      case c @ Equals(_, _: FunctionInvocation) => Set[Expr](c)
      case _ => Set[Expr]()
    } _
    val specCalls = callCollect(flatAssump) ++ callCollect(conseqNeg)
    val vc = createAnd(Seq(flatAssump, flatBody, conseqNeg))
    funcVCs += (fd -> new Formula(fd, vc, ctx, specCalls))
  }

  def initialize = {
    //assume specifications
    specInstantiator.instantiate
  }

  def refineVCs(toUnrollCalls: Option[Set[Call]]) : Set[Call]  = {
    val unrolledCalls = vcRefiner.refineAbstraction(toUnrollCalls)
    specInstantiator.instantiate
    unrolledCalls
  }
}
