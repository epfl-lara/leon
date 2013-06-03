/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

case object InequalitySplit extends Rule("Ineq. Split.") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val solver = sctx.simpleSolver

    val candidates = p.as.filter(_.getType == Int32Type).combinations(2).toList.filter {
      case List(a1, a2) =>
        val toValLT = Implies(p.pc, LessThan(Variable(a1), Variable(a2)))

        val impliesLT = solver.solveSAT(Not(toValLT)) match {
          case (Some(false), _) => true
          case _ => false
        }

        if (!impliesLT) {
          val toValGT = Implies(p.pc, GreaterThan(Variable(a1), Variable(a2)))

          val impliesGT = solver.solveSAT(Not(toValGT)) match {
            case (Some(false), _) => true
            case _ => false
          }

          if (!impliesGT) {
            val toValEQ = Implies(p.pc, Equals(Variable(a1), Variable(a2)))

            val impliesEQ = solver.solveSAT(Not(toValEQ)) match {
              case (Some(false), _) => true
              case _ => false
            }

            !impliesEQ
          } else {
            false
          }
        } else {
          false
        }
      case _ => false
    }


    candidates.flatMap(_ match {
      case List(a1, a2) =>

        val subLT = p.copy(pc = And(LessThan(Variable(a1), Variable(a2)), p.pc))
        val subEQ = p.copy(pc = And(Equals(Variable(a1), Variable(a2)), p.pc))
        val subGT = p.copy(pc = And(GreaterThan(Variable(a1), Variable(a2)), p.pc))

        val onSuccess: List[Solution] => Option[Solution] = { 
          case sols @ List(sLT, sEQ, sGT) =>
            val pre  = Or(sols.map(_.pre))
            val defs = sLT.defs ++ sEQ.defs ++ sGT.defs

            val term = IfExpr(LessThan(Variable(a1), Variable(a2)),
                              sLT.term,
                              IfExpr(Equals(Variable(a1), Variable(a2)),
                                     sEQ.term,
                                     sGT.term))

            Some(Solution(pre, defs, term))
          case _ =>
            None
        }

        Some(RuleInstantiation.immediateDecomp(p, this, List(subLT, subEQ, subGT), onSuccess, "Ineq. Split on '"+a1+"' and '"+a2+"'"))
      case _ =>
        None
    })
  }
}
