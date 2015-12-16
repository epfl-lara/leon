package leon
package invariant.engine

import purescala.Definitions._
import purescala.Expressions._
import invariant.structure._

class ConstraintTracker(ctx : InferenceContext, program: Program, rootFun : FunDef/*, temFactory: TemplateFactory*/) {

  //a mapping from functions to its VCs represented as a CNF formula
  protected var funcVCs = Map[FunDef,Formula]()

  val vcRefiner = new RefinementEngine(ctx, program, this)
  val specInstantiator = new SpecInstantiator(ctx, program, this)

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
