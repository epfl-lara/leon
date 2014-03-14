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

      val solver = SimpleSolverAPI(new TimeoutSolverFactory(sctx.solverFactory, 5000L))

      val tpe = TupleType(p.xs.map(_.getType))

      val result = solver.solveSAT(p.phi) match {
        case (Some(true), model) =>
          val sol = Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(model))).setType(tpe))
          Some(RuleInstantiation.immediateSuccess(p, this, sol))
        case (Some(false), model) =>
          val sol = Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe))
          Some(RuleInstantiation.immediateSuccess(p, this, sol))
        case _ =>
          None
      }

      result
    } else {
      None
    }
  }
}

