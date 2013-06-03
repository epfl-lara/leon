/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import solvers.TimeoutSolver
import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

case object Ground extends Rule("Ground") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    if (p.as.isEmpty) {

      val solver = new TimeoutSolver(sctx.solver, 5000L) // We give that 1s

      val tpe = TupleType(p.xs.map(_.getType))

      solver.solveSAT(p.phi) match {
        case (Some(true), model) =>
          val sol = Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(model))).setType(tpe))
          Some(RuleInstantiation.immediateSuccess(p, this, sol))
        case (Some(false), model) =>
          val sol = Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe))
          Some(RuleInstantiation.immediateSuccess(p, this, sol))
        case _ =>
          None
      }
    } else {
      None
    }
  }
}

