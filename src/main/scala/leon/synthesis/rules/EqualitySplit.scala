package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Common._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

case object EqualitySplit extends Rule("Eq. Split.") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val candidates = p.as.groupBy(_.getType).map(_._2.toList).filter {
      case List(a1, a2) =>
        val toValEQ = Implies(p.pc, Equals(Variable(a1), Variable(a2)))

        val impliesEQ = sctx.solver.solveSAT(Not(toValEQ)) match {
          case (Some(false), _) => true
          case _ => false
        }

        if (!impliesEQ) {
          val toValNE = Implies(p.pc, Not(Equals(Variable(a1), Variable(a2))))

          val impliesNE = sctx.solver.solveSAT(Not(toValNE)) match {
            case (Some(false), _) => true
            case _ => false
          }

          !impliesNE
        } else {
          false
        }
      case _ => false
    }


    candidates.map(_ match {
      case List(a1, a2) =>

        val sub1 = p.copy(pc = And(Equals(Variable(a1), Variable(a2)), p.pc))
        val sub2 = p.copy(pc = And(Not(Equals(Variable(a1), Variable(a2))), p.pc))

        val onSuccess: List[Solution] => Option[Solution] = { 
          case List(s1, s2) =>
            Some(Solution(Or(s1.pre, s2.pre), s1.defs++s2.defs, IfExpr(Equals(Variable(a1), Variable(a2)), s1.term, s2.term)))
          case _ =>
            None
        }

        Some(RuleInstantiation.immediateDecomp(p, this, List(sub1, sub2), onSuccess))
      case _ =>
        None
    }).flatten
  }
}
