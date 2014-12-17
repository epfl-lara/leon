/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Constructors._

import solvers._

case object InequalitySplit extends Rule("Ineq. Split.") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val solver = SimpleSolverAPI(sctx.fastSolverFactory)

    val candidates = p.as.filter(_.getType == Int32Type).combinations(2).toList.filter {
      case List(a1, a2) =>
        val toValLT = implies(p.pc, LessThan(Variable(a1), Variable(a2)))

        val impliesLT = solver.solveSAT(not(toValLT)) match {
          case (Some(false), _) => true
          case _ => false
        }

        if (!impliesLT) {
          val toValGT = implies(p.pc, GreaterThan(Variable(a1), Variable(a2)))

          val impliesGT = solver.solveSAT(not(toValGT)) match {
            case (Some(false), _) => true
            case _ => false
          }

          if (!impliesGT) {
            val toValEQ = implies(p.pc, Equals(Variable(a1), Variable(a2)))

            val impliesEQ = solver.solveSAT(not(toValEQ)) match {
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

        val subLT = p.copy(pc = and(LessThan(Variable(a1), Variable(a2)), p.pc))
        val subEQ = p.copy(pc = and(Equals(Variable(a1), Variable(a2)), p.pc))
        val subGT = p.copy(pc = and(GreaterThan(Variable(a1), Variable(a2)), p.pc))

        val onSuccess: List[Solution] => Option[Solution] = { 
          case sols @ List(sLT, sEQ, sGT) =>
            val pre  = orJoin(sols.map(_.pre))
            val defs = sLT.defs ++ sEQ.defs ++ sGT.defs

            val term = IfExpr(LessThan(Variable(a1), Variable(a2)),
                              sLT.term,
                              IfExpr(Equals(Variable(a1), Variable(a2)),
                                     sEQ.term,
                                     sGT.term))

            Some(Solution(pre, defs, term, sols.forall(_.isTrusted)))
          case _ =>
            None
        }

        Some(RuleInstantiation.immediateDecomp(p, this, List(subLT, subEQ, subGT), onSuccess, "Ineq. Split on '"+a1+"' and '"+a2+"'"))
      case _ =>
        None
    })
  }
}
