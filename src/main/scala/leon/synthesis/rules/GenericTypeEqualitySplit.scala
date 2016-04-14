/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.purescala.Common.Identifier
import purescala.Constructors._
import purescala.Expressions._
import leon.purescala.Extractors.{IsTyped, TopLevelAnds}
import purescala.Types._

/** For every pair of input variables of the same generic type,
  * checks equality and output an If-Then-Else statement with the two new branches.
  */
case object GenericTypeEqualitySplit extends Rule("Eq. Split") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    // We approximate knowledge of equality based on facts found at the top-level
    // we don't care if the variables are known to be equal or not, we just
    // don't want to split on two variables for which only one split
    // alternative is viable. This should be much less expensive than making
    // calls to a solver for each pair.
    def getFacts(e: Expr): Set[Set[Identifier]] = e match {
      case Not(e)       => getFacts(e)
      case Equals(Variable(a), Variable(b)) => Set(Set(a,b))
      case _ => Set()
    }

    val facts: Set[Set[Identifier]] = {
      val TopLevelAnds(as) = andJoin(p.pc.conditions :+ p.phi)
      as.toSet.flatMap(getFacts)
    }

    val candidates = p.allAs.combinations(2).collect {
      case List(IsTyped(a1, TypeParameter(t1)), IsTyped(a2, TypeParameter(t2)))
        if t1 == t2 && !facts(Set(a1, a2)) =>
        (a1, a2)
    }.toList

    candidates.flatMap {
      case (a1, a2) =>
        val v1 = Variable(a1)
        val v2 = Variable(a2)
        val subProblems = List(
          p.copy(as  = p.as.diff(Seq(a1)),
                 pc  = p.pc map (subst(a1 -> v2, _)),
                 ws  = subst(a1 -> v2, p.ws),
                 phi = subst(a1 -> v2, p.phi),
                 eb  = p.qeb.filterIns(Equals(v1, v2)).removeIns(Set(a1))),

          p.copy(pc = p.pc withCond not(Equals(v1, v2)),
                 eb = p.qeb.filterIns(not(Equals(v1, v2))))
        )

        val onSuccess: List[Solution] => Option[Solution] = {
          case sols @ List(sEQ, sNE) =>
            val pre = or(
              and(Equals(v1, v2),      sEQ.pre),
              and(not(Equals(v1, v2)), sNE.pre)
            )

            val term = IfExpr(Equals(v1, v2), sEQ.term, sNE.term)

            Some(Solution(pre, sols.flatMap(_.defs).toSet, term, sols.forall(_.isTrusted)))
        }

        Some(decomp(subProblems, onSuccess, s"Eq. Split on '$v1' and '$v2'"))

      case _ =>
        None
    }
  }
}
