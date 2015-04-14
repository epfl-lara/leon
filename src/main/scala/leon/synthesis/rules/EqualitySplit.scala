/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Constructors._

import solvers._

case object EqualitySplit extends Rule("Eq. Split") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val solver = SimpleSolverAPI(hctx.sctx.fastSolverFactory)

    val candidates = p.as.groupBy(_.getType).mapValues(_.combinations(2).filter {
      case List(a1, a2) =>
        val toValEQ = implies(p.pc, Equals(Variable(a1), Variable(a2)))

        val impliesEQ = solver.solveSAT(Not(toValEQ)) match {
          case (Some(false), _) => true
          case _ => false
        }

        if (!impliesEQ) {
          val toValNE = implies(p.pc, not(Equals(Variable(a1), Variable(a2))))

          val impliesNE = solver.solveSAT(Not(toValNE)) match {
            case (Some(false), _) => true
            case _ => false
          }

          !impliesNE
        } else {
          false
        }
      case _ => false
    }).values.flatten

    candidates.flatMap {
      case List(a1, a2) =>

        val sub1 = p.copy(pc = and(Equals(Variable(a1), Variable(a2)), p.pc))
        val sub2 = p.copy(pc = and(not(Equals(Variable(a1), Variable(a2))), p.pc))

        val onSuccess: List[Solution] => Option[Solution] = {
          case List(s1, s2) =>
            Some(Solution(or(s1.pre, s2.pre), s1.defs ++ s2.defs, IfExpr(Equals(Variable(a1), Variable(a2)), s1.term, s2.term), s1.isTrusted && s2.isTrusted))
          case _ =>
            None
        }

        Some(decomp(List(sub1, sub2), onSuccess, s"Eq. Split on '$a1' and '$a2'"))
      case _ =>
        None
    }
  }
}
