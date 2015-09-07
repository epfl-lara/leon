/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Expressions._
import purescala.Types._
import purescala.ExprOps._
import purescala.Constructors.and
import rules._

/** A Rule can be applied on a synthesis problem */
abstract class Rule(val name: String) extends RuleDSL {
  def instantiateOn(implicit hctx: SearchContext, problem: Problem): Traversable[RuleInstantiation]

  val priority: RulePriority = RulePriorityDefault

  implicit val debugSection = leon.utils.DebugSectionSynthesis

  implicit val thisRule = this

  implicit def hctxToCtx(implicit hctx: SearchContext): LeonContext = hctx.sctx.context

  def asString(implicit ctx: LeonContext) = name
}

abstract class NormalizingRule(name: String) extends Rule(name) {
  override val priority = RulePriorityNormalizing
}

abstract class PreprocessingRule(name: String) extends Rule(name) {
  override val priority = RulePriorityPreprocessing
}

/** Contains the list of all available rules for synthesis */
object Rules {
  /** Returns the list of all available rules for synthesis */
  def all = List[Rule](
    Unification.DecompTrivialClash,
    Unification.OccursCheck, // probably useless
    Disunification.Decomp,
    ADTDual,
    //OnePoint,
    Ground,
    CaseSplit,
    IfSplit,
    UnusedInput,
    EquivalentInputs,
    UnconstrainedOutput,
    OptimisticGround,
    EqualitySplit,
    InequalitySplit,
    CEGIS,
    TEGIS,
    //BottomUpTEGIS,
    rules.Assert,
    DetupleOutput,
    DetupleInput,
    ADTSplit,
    //IntegerEquation,
    //IntegerInequalities,
    IntInduction,
    InnerCaseSplit
    //new OptimisticInjection(_),
    //new SelectiveInlining(_),
    //ADTLongInduction,
    //ADTInduction
    //AngelicHoles // @EK: Disabled now as it is explicit with withOracle { .. }
  )

}

abstract class RuleInstantiation(val description: String,
                                 val onSuccess: SolutionBuilder = SolutionBuilderCloser())
                                (implicit val problem: Problem, val rule: Rule) {

  def apply(hctx: SearchContext): RuleApplication

  def asString(implicit ctx: LeonContext) = description
}

/**
 * Wrapper class for a function returning a recomposed solution from a list of
 * subsolutions
 *
 * We also need to know the types of the expected sub-solutions to use them in
 * cost-models before having real solutions.
 */
abstract class SolutionBuilder {
  val types: Seq[TypeTree]

  def apply(sols: List[Solution]): Option[Solution]
}

case class SolutionBuilderDecomp(types: Seq[TypeTree], recomp: List[Solution] => Option[Solution]) extends SolutionBuilder {
  def apply(sols: List[Solution]): Option[Solution] = {
    assert(types.size == sols.size)
    recomp(sols)
  }
}

/**
 * Used by rules expected to close, no decomposition but maybe we already know
 * the solution when instantiating
 */
case class SolutionBuilderCloser(osol: Option[Solution] = None) extends SolutionBuilder {
  val types = Nil
  def apply(sols: List[Solution]) = {
    assert(sols.isEmpty)
    osol
  }
}

/**
 * Results of applying rule instantiations
 *
 * Can either close meaning a stream of solutions are available (can be empty,
 * if it failed)
 */
sealed abstract class RuleApplication
case class RuleClosed(solutions: Stream[Solution]) extends RuleApplication
case class RuleExpanded(sub: List[Problem])        extends RuleApplication

object RuleClosed {
  def apply(s: Solution): RuleClosed = RuleClosed(Stream(s))
}

object RuleFailed {
  def apply(): RuleClosed = RuleClosed(Stream.empty)
}

/**
 * Rule priorities, which drive the instantiation order.
 */
sealed abstract class RulePriority(val v: Int) extends Ordered[RulePriority] {
  def compare(that: RulePriority) = this.v - that.v
}

case object RulePriorityPreprocessing extends RulePriority(5)
case object RulePriorityNormalizing   extends RulePriority(10)
case object RulePriorityHoles         extends RulePriority(15)
case object RulePriorityDefault       extends RulePriority(20)

/**
 * Common utilities used by rules
 */
trait RuleDSL {
  this: Rule =>
  /** Replaces all first elements of `what` by their second element in the expression `ìn`*/
  def subst(what: (Identifier, Expr), in: Expr): Expr = replaceFromIDs(Map(what), in)
  /** Replaces all keys of `what` by their key in the expression `ìn`*/
  def substAll(what: Map[Identifier, Expr], in: Expr): Expr = replaceFromIDs(what, in)

  val forward: List[Solution] => Option[Solution] = { ss => ss.headOption }
  
  /** Returns a function that transforms the precondition and term of the first Solution of a list using `f`.  */
  def forwardMap(f : Expr => Expr) : List[Solution] => Option[Solution] = { 
    _.headOption map { s =>
      Solution(f(s.pre), s.defs, f(s.term), s.isTrusted)
    }
  }

  def decomp(sub: List[Problem], onSuccess: List[Solution] => Option[Solution], description: String)
            (implicit problem: Problem): RuleInstantiation = {

    val subTypes = sub.map(_.outType)

    new RuleInstantiation(description,
                          SolutionBuilderDecomp(subTypes, onSuccess)) {
      def apply(hctx: SearchContext) = RuleExpanded(sub)
    }
  }

  def solve(sol: Solution)
           (implicit problem: Problem, ctx: LeonContext): RuleInstantiation = {

    new RuleInstantiation(s"Solve: ${sol.asString}",
                          SolutionBuilderCloser(Some(sol))) {
      def apply(hctx: SearchContext) = RuleClosed(sol)
    }

  }

  // pc corresponds to the pc to reach the point where the solution is used. It
  // will be used if the sub-solution has a non-true pre.
  def termWrap(f: Expr => Expr, pc: Expr = BooleanLiteral(true)): List[Solution] => Option[Solution] = {
    case List(s) =>
      val pre = if (s.pre == BooleanLiteral(true)) {
        BooleanLiteral(true)
      } else {
        and(pc, s.pre)
      }

      Some(Solution(pre, s.defs, f(s.term), s.isTrusted))
    case _ => None

  }
}
