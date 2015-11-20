/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Types._
import purescala.Constructors._
import purescala.Extractors._
import purescala.Common._

import scala.concurrent.duration._

case object InequalitySplit extends Rule("Ineq. Split.") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    // We approximate knowledge of equality based on facts found at the top-level
    // we don't care if the variables are known to be equal or not, we just
    // don't want to split on two variables for which only one split
    // alternative is viable. This should be much less expensive than making
    //  calls to a solver for each pair.
    var facts = Set[Set[Identifier]]()

    def addFacts(e: Expr): Unit = e match {
      case Not(e) => addFacts(e)
      case LessThan(Variable(a), Variable(b))      => facts += Set(a,b)
      case LessEquals(Variable(a), Variable(b))    => facts += Set(a,b)
      case GreaterThan(Variable(a), Variable(b))   => facts += Set(a,b)
      case GreaterEquals(Variable(a), Variable(b)) => facts += Set(a,b)
      case Equals(Variable(a), Variable(b))        => facts += Set(a,b)
      case _ =>
    }

    val TopLevelAnds(as) = and(p.pc, p.phi)
    for (e <- as) {
      addFacts(e)
    }

    val argsPairs = p.as.filter(_.getType == IntegerType).combinations(2) ++
                    p.as.filter(_.getType == Int32Type).combinations(2)

    val candidates = argsPairs.toList.filter { case List(a1, a2) => !(facts contains Set(a1, a2)) }

    candidates.flatMap {
      case List(a1, a2) =>
        val subLT = p.copy(pc = and(LessThan(Variable(a1), Variable(a2)), p.pc),
                           eb = p.qeb.filterIns(LessThan(Variable(a1), Variable(a2))))
        val subEQ = p.copy(pc = and(Equals(Variable(a1), Variable(a2)), p.pc),
                           eb = p.qeb.filterIns(Equals(Variable(a1), Variable(a2))))
        val subGT = p.copy(pc = and(GreaterThan(Variable(a1), Variable(a2)), p.pc),
                           eb = p.qeb.filterIns(GreaterThan(Variable(a1), Variable(a2))))

        val onSuccess: List[Solution] => Option[Solution] = {
          case sols@List(sLT, sEQ, sGT) =>
            val pre = orJoin(sols.map(_.pre))
            val defs = sLT.defs ++ sEQ.defs ++ sGT.defs

            val term = IfExpr(
              LessThan(Variable(a1), Variable(a2)),
              sLT.term,
              IfExpr(
                Equals(Variable(a1), Variable(a2)),
                sEQ.term,
                sGT.term
              )
            )

            Some(Solution(pre, defs, term, sols.forall(_.isTrusted)))
          case _ =>
            None
        }

        Some(decomp(List(subLT, subEQ, subGT), onSuccess, s"Ineq. Split on '$a1' and '$a2'"))
      case _ =>
        None
    }
  }
}
