/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import solvers._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Constructors._
import scala.concurrent.duration._

case object Ground extends Rule("Ground") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    if (p.as.isEmpty) {
      List(new RuleInstantiation(this.name) {
        def apply(hctx: SearchContext): RuleApplication = {
          val solver = SimpleSolverAPI(hctx.sctx.solverFactory.withTimeout(10.seconds))

          val result = solver.solveSAT(p.phi) match {
            case (Some(true), model) =>
              val sol = Solution(BooleanLiteral(true), Set(), tupleWrap(p.xs.map(valuateWithModel(model))))
              RuleClosed(sol)
            case (Some(false), model) =>
              RuleClosed(Solution.UNSAT(p))
            case _ =>
              RuleFailed()
          }

          result
        }
      })
    } else {
      None
    }
  }
}

