/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import rules._

object Rules {
  def all = List[Rule](
    Unification.DecompTrivialClash,
    Unification.OccursCheck, // probably useless
    Disunification.Decomp,
    ADTDual,
    OnePoint,
    Ground,
    CaseSplit,
    IfSplit,
    UnusedInput,
    UnconstrainedOutput,
    OptimisticGround,
    EqualitySplit,
    InequalitySplit,
    CEGIS,
    TEGIS,
    GuidedDecomp,
    GuidedCloser,
    rules.Assert,
    DetupleOutput,
    DetupleInput,
    ADTSplit,
    InlineHoles,
    IntegerEquation,
    IntegerInequalities
    //AngelicHoles // @EK: Disabled now as it is explicit with withOracle { .. }
  )

  def getInstantiations(sctx: SynthesisContext, problem: Problem) = {
    val sub = sctx.rules.flatMap { r =>
      r.instantiateOn(sctx, problem)
    }

    val res = sub.groupBy(_.priority).toSeq.sortBy(_._1)

    if (res.nonEmpty) {
      res.head._2.toList
    } else {
      Nil
    }
  }
}

abstract class SolutionBuilder(val arity: Int, val types: Seq[TypeTree]) {
  def apply(sols: List[Solution]): Option[Solution]

  assert(types.size == arity)
}

class SolutionCombiner(arity: Int, types: Seq[TypeTree],  f: List[Solution] => Option[Solution]) extends SolutionBuilder(arity, types) {
  def apply(sols: List[Solution]) = {
    assert(sols.size == arity)
    f(sols)
  }
}

object SolutionBuilder {
  val none = new SolutionBuilder(0, Seq()) {
    def apply(sols: List[Solution]) = None
  }
}

abstract class RuleInstantiation(
  val problem: Problem,
  val rule: Rule,
  val onSuccess: SolutionBuilder,
  val description: String,
  val priority: RulePriority) {

  def apply(sctx: SynthesisContext): RuleApplication

  override def toString = description
}

sealed abstract class RuleApplication
case class RuleClosed(solutions: Stream[Solution]) extends RuleApplication
case class RuleExpanded(sub: List[Problem])        extends RuleApplication

object RuleClosed {
  def apply(s: Solution): RuleClosed = RuleClosed(Stream(s))
}

object RuleFailed {
  def apply(): RuleClosed = RuleClosed(Stream.empty)
}

sealed abstract class RulePriority(val v: Int) extends Ordered[RulePriority] {
  def compare(that: RulePriority) = this.v - that.v
}

case object RulePriorityDefault     extends RulePriority(2)
case object RulePriorityNormalizing extends RulePriority(0)
case object RulePriorityHoles       extends RulePriority(1)

object RuleInstantiation {
  def immediateDecomp(problem: Problem,
                      rule: Rule,
                      sub: List[Problem],
                      onSuccess: List[Solution] => Option[Solution]): RuleInstantiation = {

    immediateDecomp(problem, rule, sub, onSuccess, rule.name, rule.priority)
  }

  def immediateDecomp(problem: Problem,
                      rule: Rule,
                      sub: List[Problem],
                      onSuccess: List[Solution] => Option[Solution],
                      description: String): RuleInstantiation = {
    immediateDecomp(problem, rule, sub, onSuccess, description, rule.priority)
  }

  def immediateDecomp(problem: Problem,
                      rule: Rule,
                      sub: List[Problem],
                      onSuccess: List[Solution] => Option[Solution],
                      description: String,
                      priority: RulePriority): RuleInstantiation = {
    val subTypes = sub.map(p => TupleType(p.xs.map(_.getType)))

    new RuleInstantiation(problem, rule, new SolutionCombiner(sub.size, subTypes, onSuccess), description, priority) {
      def apply(sctx: SynthesisContext) = RuleExpanded(sub)
    }
  }

  def immediateSuccess(problem: Problem,
                       rule: Rule,
                       solution: Solution): RuleInstantiation = {
    immediateSuccess(problem, rule, solution, rule.priority)

  }

  def immediateSuccess(problem: Problem,
                       rule: Rule,
                       solution: Solution,
                       priority: RulePriority): RuleInstantiation = {
    new RuleInstantiation(problem, rule, new SolutionCombiner(0, Seq(), ls => Some(solution)), "Solve with "+solution, priority) {
      def apply(sctx: SynthesisContext) = RuleClosed(solution)
    }
  }
}

abstract class Rule(val name: String) extends RuleHelpers {
  def instantiateOn(sctx: SynthesisContext, problem: Problem): Traversable[RuleInstantiation]

  val priority: RulePriority = RulePriorityDefault

  implicit val debugSection = leon.utils.DebugSectionSynthesis

  override def toString = "R: "+name
}

abstract class NormalizingRule(name: String) extends Rule(name) {
  override val priority = RulePriorityNormalizing
}

trait RuleHelpers {
  def subst(what: Tuple2[Identifier, Expr], in: Expr): Expr = replaceFromIDs(Map(what), in)
  def substAll(what: Map[Identifier, Expr], in: Expr): Expr = replaceFromIDs(what, in)

  val forward: List[Solution] => Option[Solution] = {
    case List(s) =>
      Some(Solution(s.pre, s.defs, s.term))
    case _ =>
      None
  }

  def project(firstN: Int): List[Solution] => Option[Solution] = {
    project(0 until firstN)
  }


  def project(ids: Seq[Int]): List[Solution] => Option[Solution] = {
    case List(s) =>
      Some(s.project(ids))
    case _ =>
      None
  }
}
