package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import rules._

object Rules {
  def all = Set[Synthesizer => Rule](
    new Unification.DecompTrivialClash(_),
    new Unification.OccursCheck(_),
    new ADTDual(_),
    new OnePoint(_),
    new Ground(_),
    new CaseSplit(_),
    new UnusedInput(_),
    new UnconstrainedOutput(_),
    new OptimisticGround(_),
    new EqualitySplit(_),
    new CEGIS(_),
    new Assert(_),
    new ADTSplit(_),
    new IntegerEquation(_),
    new IntegerInequalities(_)
  )
}

sealed abstract class RuleResult
case object RuleInapplicable extends RuleResult
case class RuleSuccess(solution: Solution) extends RuleResult
case class RuleAlternatives(steps: Set[RuleMultiSteps]) extends RuleResult

case class RuleMultiSteps(subProblems: List[Problem],
                          interSteps: List[List[Solution] => List[Problem]],
                          onSuccess: List[Solution] => (Solution, Boolean))

object RuleStep {
  def apply(subProblems: List[Problem], onSuccess: List[Solution] => Solution) = {
    RuleMultiSteps(subProblems, Nil, onSuccess.andThen((_, true)))
  }
}

object RuleOneStep {
  def apply(subProblems: List[Problem], onSuccess: List[Solution] => Solution) = {
    RuleAlternatives(Set(RuleStep(subProblems, onSuccess)))
  }
}

abstract class Rule(val name: String, val synth: Synthesizer, val priority: Priority) {
  def applyOn(task: Task): RuleResult

  def subst(what: Tuple2[Identifier, Expr], in: Expr): Expr = replace(Map(Variable(what._1) -> what._2), in)
  def substAll(what: Map[Identifier, Expr], in: Expr): Expr = replace(what.map(w => Variable(w._1) -> w._2), in)

  val forward: List[Solution] => Solution = {
    case List(s) => Solution(s.pre, s.defs, s.term)
    case _ => Solution.none
  }

  override def toString = "R: "+name
}
