/* Copyright 2009-2013 EPFL, Lausanne */

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
    UnusedInput,
    UnconstrainedOutput,
    OptimisticGround,
    EqualitySplit,
    InequalitySplit,
    CEGIS,
    Assert,
    DetupleOutput,
    DetupleInput,
    ADTSplit,
    IntegerEquation,
    IntegerInequalities
  )
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

abstract class RuleInstantiation(val problem: Problem, val rule: Rule, val onSuccess: SolutionBuilder, val description: String) {
  def apply(sctx: SynthesisContext): RuleApplicationResult

  override def toString = description
}

sealed abstract class RuleApplicationResult
case class RuleSuccess(solution: Solution, isTrusted: Boolean = true)  extends RuleApplicationResult
case class RuleDecomposed(sub: List[Problem])                          extends RuleApplicationResult
case object RuleApplicationImpossible                                  extends RuleApplicationResult

object RuleInstantiation {
  def immediateDecomp(problem: Problem, rule: Rule, sub: List[Problem], onSuccess: List[Solution] => Option[Solution], description: String) = {
    val subTypes = sub.map(p => TupleType(p.xs.map(_.getType)))

    new RuleInstantiation(problem, rule, new SolutionCombiner(sub.size, subTypes, onSuccess), description) {
      def apply(sctx: SynthesisContext) = RuleDecomposed(sub)
    }
  }

  def immediateSuccess(problem: Problem, rule: Rule, solution: Solution) = {
    new RuleInstantiation(problem, rule, new SolutionCombiner(0, Seq(), ls => Some(solution)), "Solve with "+solution) {
      def apply(sctx: SynthesisContext) = RuleSuccess(solution)
    }
  }
}

abstract class Rule(val name: String) {
  def instantiateOn(sctx: SynthesisContext, problem: Problem): Traversable[RuleInstantiation]

  def subst(what: Tuple2[Identifier, Expr], in: Expr): Expr = replace(Map(Variable(what._1) -> what._2), in)
  def substAll(what: Map[Identifier, Expr], in: Expr): Expr = replace(what.map(w => Variable(w._1) -> w._2), in)

  implicit val debugSection = DebugSectionSynthesis

  val forward: List[Solution] => Option[Solution] = {
    case List(s) =>
      Some(Solution(s.pre, s.defs, s.term))
    case _ =>
      None
  }

  override def toString = "R: "+name
}

// Note: Rules that extend NormalizingRule should all be commutative, The will
// be applied before others in a deterministic order and their application
// should never fail!
abstract class NormalizingRule(name: String) extends Rule(name) {
  override def toString = "N: "+name
}
