package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object OnePoint extends Rule("One-point") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val TopLevelAnds(exprs) = p.phi

    val candidates = exprs.collect {
      case eq @ Equals(Variable(x), e) if (p.xs contains x) && !(variablesOf(e) contains x) =>
        (x, e, eq)
      case eq @ Equals(e, Variable(x)) if (p.xs contains x) && !(variablesOf(e) contains x) =>
        (x, e, eq)
    }

    if (!candidates.isEmpty) {
      val (x, e, eq) = candidates.head

      val others = exprs.filter(_ != eq)
      val oxs    = p.xs.filter(_ != x)

      val newProblem = Problem(p.as, p.pc, subst(x -> e, And(others)), oxs)

      val onSuccess: List[Solution] => Solution = { 
        case List(Solution(pre, defs, term)) =>
          if (oxs.isEmpty) {
            Solution(pre, defs, Tuple(e :: Nil)) 
          } else {
            Solution(pre, defs, LetTuple(oxs, term, subst(x -> e, Tuple(p.xs.map(Variable(_)))))) 
          }
        case _ => Solution.none
      }

      List(RuleInstantiation.immediateDecomp(p, this, List(newProblem), onSuccess))
    } else {
      Nil
    }
  }
}

