package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import rules._

object Rules {
  def all = Set[Rule](
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
    CEGIS,
    Assert,
    ADTSplit,
    IntegerEquation,
    IntegerInequalities
  )
}

abstract class SolutionBuilder(val arity: Int) {
  def apply(sols: List[Solution]): Option[Solution]
}

class SolutionCombiner(arity: Int, f: List[Solution] => Option[Solution]) extends SolutionBuilder(arity) {
  def apply(sols: List[Solution]) = {
    assert(sols.size == arity)
    f(sols)
  }
}

object SolutionBuilder {
  val none = new SolutionBuilder(0) {
    def apply(sols: List[Solution]) = None
  }
}

abstract class RuleInstantiation(val problem: Problem, val rule: Rule, val onSuccess: SolutionBuilder) {
  def apply(sctx: SynthesisContext): RuleApplicationResult
}

//abstract class RuleApplication(val subProblemsCount: Int,
//                               val onSuccess: List[Solution] => Solution) {
//
//  def apply(sctx: SynthesisContext): RuleApplicationResult
//}
//
//abstract class RuleImmediateApplication extends RuleApplication(0, s => Solution.simplest)

sealed abstract class RuleApplicationResult
case class RuleSuccess(solution: Solution)    extends RuleApplicationResult
case class RuleDecomposed(sub: List[Problem]) extends RuleApplicationResult
case object RuleApplicationImpossible         extends RuleApplicationResult

object RuleInstantiation {
  def immediateDecomp(problem: Problem, rule: Rule, sub: List[Problem], onSuccess: List[Solution] => Option[Solution]) = {
    new RuleInstantiation(problem, rule, new SolutionCombiner(sub.size, onSuccess)) {
      def apply(sctx: SynthesisContext) = RuleDecomposed(sub)
    }
  }

  def immediateSuccess(problem: Problem, rule: Rule, solution: Solution) = {
    new RuleInstantiation(problem, rule, new SolutionCombiner(0, ls => Some(solution))) {
      def apply(sctx: SynthesisContext) = RuleSuccess(solution)
    }
  }
}

abstract class Rule(val name: String) {
  def instantiateOn(scrx: SynthesisContext, problem: Problem): Traversable[RuleInstantiation]

  def subst(what: Tuple2[Identifier, Expr], in: Expr): Expr = replace(Map(Variable(what._1) -> what._2), in)
  def substAll(what: Map[Identifier, Expr], in: Expr): Expr = replace(what.map(w => Variable(w._1) -> w._2), in)

  val forward: List[Solution] => Option[Solution] = {
    case List(s) =>
      Some(Solution(s.pre, s.defs, s.term))
    case _ =>
      None
  }

  override def toString = "R: "+name
}
