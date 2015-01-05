/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import solvers._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Constructors._

case object Ground extends Rule("Ground") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    if (p.as.isEmpty) {
      List(new RuleInstantiation(this.name) {
        def apply(hctx: SearchContext): RuleApplication = {
          val solver = SimpleSolverAPI(new TimeoutSolverFactory(hctx.sctx.solverFactory, 10000L))

          val tpe = tupleTypeWrap(p.xs.map(_.getType))

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

