package leon
package invariant.engine

import z3.scala._
import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import evaluators._
import java.io._

import invariant.factories._
import invariant.util._
import invariant.structure._

class ConstraintTracker(ctx : InferenceContext, rootFun : FunDef/*, temFactory: TemplateFactory*/) {

  //a mapping from functions to its VCs represented as a CNF formula
  protected var funcVCs = Map[FunDef,Formula]()

  val vcRefiner = new RefinementEngine(ctx, this/*, temFactory*/)
  val specInstantiator = new SpecInstantiator(ctx, this/*, temFactory*/)

  def getFuncs : Seq[FunDef] = funcVCs.keys.toSeq
  def hasVC(fdef: FunDef) = funcVCs.contains(fdef)
  def getVC(fd: FunDef) : Formula = funcVCs(fd)

  def addVC(fd: FunDef, vc: Expr) = {
    funcVCs += (fd -> new Formula(fd, vc, ctx))
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
