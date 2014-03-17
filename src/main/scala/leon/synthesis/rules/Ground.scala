/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import solvers._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

case object Ground extends Rule("Ground") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    if (p.as.isEmpty) {
      List(new RuleInstantiation(p, this, SolutionBuilder.none, "Ground") {
        def apply(sctx: SynthesisContext): RuleApplicationResult = {
          val solver = SimpleSolverAPI(new TimeoutSolverFactory(sctx.solverFactory, 10000L))

          val tpe = TupleType(p.xs.map(_.getType))

          val result = solver.solveSAT(p.phi) match {
            case (Some(true), model) =>
              val sol = Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(model))).setType(tpe))
              RuleSuccess(sol)
            case (Some(false), model) =>
              val sol = Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe))
              RuleSuccess(sol)
            case _ =>
              RuleApplicationImpossible
          }

          result
        }
      })
    } else {
      None
    }
  }
}

