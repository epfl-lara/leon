/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Constructors._

import solvers._

import scala.concurrent.duration._

case object OptimisticGround extends Rule("Optimistic Ground") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    if (p.as.nonEmpty && p.xs.nonEmpty) {
      val res = new RuleInstantiation(this.name) {
        def apply(hctx: SearchContext) = {

          val solver = SimpleSolverAPI(hctx.solverFactory.withTimeout(50.millis))

          val xss = p.xs.toSet
          val ass = p.as.toSet

          var i = 0
          val maxTries = 3

          var result: Option[RuleApplication] = None
          var continue                        = true
          var predicates: Seq[Expr]           = Seq()

          while (result.isEmpty && i < maxTries && continue) {
            val phi = p.pc and andJoin(p.phi +: predicates)
            val notPhi = p.pc and andJoin(not(p.phi) +: predicates)
            //println("SOLVING " + phi + " ...")
            solver.solveSAT(phi) match {
              case (Some(true), satModel) =>
                val newNotPhi = valuateWithModelIn(notPhi, xss, satModel)

                //println("REFUTING " + Not(newNotPhi) + "...")
                solver.solveSAT(newNotPhi) match {
                  case (Some(true), invalidModel) =>
                    // Found as such as the xs break, refine predicates
                    predicates = valuateWithModelIn(phi, ass, invalidModel) +: predicates

                  case (Some(false), _) =>
                    // Model appears valid, but it might be a fake expression (generic values)
                    val outExpr = tupleWrap(p.xs.map(valuateWithModel(satModel)))

                    if (!isRealExpr(outExpr)) {
                      // It does contain a generic value, we skip
                      predicates = valuateWithModelIn(phi, xss, satModel) +: predicates
                    } else {
                      result = Some(RuleClosed(Solution(BooleanLiteral(true), Set(), outExpr)))
                    }
                  case _ =>
                    continue = false
                    result = None
                }

              case (Some(false), _) =>
                if (predicates.isEmpty) {
                  result = Some(RuleClosed(Solution.UNSAT(p)))
                } else {
                  continue = false
                  result = None
                }
              case _ =>
                continue = false
                result = None
            }

            i += 1
          }

          result.getOrElse(RuleFailed())
        }
      }
      List(res)
    } else {
      Nil
    }
  }
}
