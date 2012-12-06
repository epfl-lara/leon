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

class SolutionCombiner(arity: Int, f: List[Solution] => Solution) extends SolutionBuilder(arity) {
  def apply(sols: List[Solution]) = {
    assert(sols.size == arity)
    Some(f(sols))
  }
}

object SolutionBuilder {
  val none = new SolutionBuilder(0) {
    def apply(sols: List[Solution]) = None
  }
}

abstract class RuleInstantiation(val onSuccess: SolutionBuilder) {
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
  def immediateDecomp(sub: List[Problem], onSuccess: List[Solution] => Solution) = {
    new RuleInstantiation(new SolutionCombiner(sub.size, onSuccess)) {
      def apply(sctx: SynthesisContext) = RuleDecomposed(sub)
    }
  }

  def immediateSuccess(solution: Solution) = {
    new RuleInstantiation(new SolutionCombiner(0, ls => solution)) {
      def apply(sctx: SynthesisContext) = RuleSuccess(solution)
    }
  }
}

abstract class Rule(val name: String, val priority: Priority) {
  def instantiateOn(scrx: SynthesisContext, problem: Problem): Traversable[RuleInstantiation]

  def subst(what: Tuple2[Identifier, Expr], in: Expr): Expr = replace(Map(Variable(what._1) -> what._2), in)
  def substAll(what: Map[Identifier, Expr], in: Expr): Expr = replace(what.map(w => Variable(w._1) -> w._2), in)

  val forward: List[Solution] => Solution = {
    case List(s) => Solution(s.pre, s.defs, s.term)
    case _ => Solution.none
  }

  override def toString = "R: "+name
}
