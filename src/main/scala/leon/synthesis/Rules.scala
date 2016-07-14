/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Expressions._
import purescala.Types._
import purescala.ExprOps._
import rules._

/** A Rule can be applied on a synthesis problem */
abstract class Rule(val name: String) extends RuleDSL with Printable {
  def instantiateOn(implicit hctx: SearchContext, problem: Problem): Traversable[RuleInstantiation]

  val priority: RulePriority = RulePriorityDefault

  implicit val debugSection = leon.utils.DebugSectionSynthesis

  implicit val thisRule = this

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

  def all: List[Rule] = all(false, true)
  /** Returns the list of all available rules for synthesis */
  def all(naiveGrammar: Boolean, introduceRecCalls: Boolean): List[Rule] = List[Rule](
    StringRender,
    Unification.DecompTrivialClash,
    Unification.OccursCheck, // probably useless
    Disunification.Decomp,
    ADTDual,
    OnePoint,
    Ground,
    CaseSplit,
    IndependentSplit,
    //HOFDecomp,
    //ExampleGuidedTermExploration,
    //BottomUpETE,
    IfSplit,
    InputSplit,
    UnusedInput,
    EquivalentInputs,
    UnconstrainedOutput,
    if(naiveGrammar) UnoptimizedTermExploration else SymbolicTermExploration,
    OptimisticGround,
    GenericTypeEqualitySplit,
    InequalitySplit,
    rules.Assert,
    DetupleInput,
    ADTSplit,
    InnerCaseSplit
  ) ++ introduceRecCalls.option(IntroduceRecCalls)

}

/** When applying this to a [SearchContext] it returns a wrapped stream of solutions or a new list of problems. */
abstract class RuleInstantiation(val description: String,
                                 val onSuccess: SolutionBuilder = SolutionBuilderCloser())
                                (implicit val problem: Problem, val rule: Rule) extends Printable {

  def apply(hctx: SearchContext): RuleApplication

  def asString(implicit ctx: LeonContext) = description
}

object RuleInstantiation {
  def apply(description: String)(f: => RuleApplication)(implicit problem: Problem, rule: Rule): RuleInstantiation = {
    new RuleInstantiation(description) {
      def apply(hctx: SearchContext): RuleApplication = f
    }
  }
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
case class SolutionBuilderCloser(osol: Option[Solution] = None, extraCost: Cost = Cost(0)) extends SolutionBuilder {
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
/** Result of applying rule instantiation, finished, resulting in a stream of solutions */
case class RuleClosed(solutions: Stream[Solution]) extends RuleApplication
/** Result of applying rule instantiation, resulting is a nnew list of problems */
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

  /** Groups sub-problems and a callback merging the solutions to produce a global solution.*/
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

  /* Utilities which implement standard onSuccess fields for decomp */

  /** Forwards a solution unchanged */
  val forward: List[Solution] => Option[Solution] = { ss => ss.headOption }

  /** Wraps term and precondition of a single [[Solution]] with given functions */
  def wrap(preWrapper: Expr => Expr, termWrapper: Expr => Expr): List[Solution] => Option[Solution] = {
    case List(Solution(pre, defs, term, isTrusted)) =>
      Some(Solution(preWrapper(pre), defs, termWrapper(term), isTrusted))
    case _ =>
      None
  }

  /** Wraps term and precondition of a single [[Solution]] with the same function */
  def simpleWrap(f: Expr => Expr) = wrap(f, f)

  /** Wrap the term of a [[Solution]] with a function. */
  def termWrap(f: Expr => Expr): List[Solution] => Option[Solution] = wrap(e => e, f)
}
