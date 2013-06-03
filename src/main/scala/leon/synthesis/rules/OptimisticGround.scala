/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

case object OptimisticGround extends Rule("Optimistic Ground") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    if (!p.as.isEmpty && !p.xs.isEmpty) {
      val res = new RuleInstantiation(p, this, SolutionBuilder.none, this.name) {
        def apply(sctx: SynthesisContext) = {

          val solver = sctx.simpleSolver // Optimistic ground is given a simple solver (uninterpreted)

          val xss = p.xs.toSet
          val ass = p.as.toSet

          val tpe = TupleType(p.xs.map(_.getType))

          var i = 0;
          var maxTries = 3;

          var result: Option[RuleApplicationResult] = None
          var continue                              = true
          var predicates: Seq[Expr]                 = Seq()

          while (result.isEmpty && i < maxTries && continue) {
            val phi = And(p.pc +: p.phi +: predicates)
            //println("SOLVING " + phi + " ...")
            solver.solveSAT(phi) match {
              case (Some(true), satModel) =>
                val satXsModel = satModel.filterKeys(xss) 

                val newPhi = valuateWithModelIn(phi, xss, satModel)

                //println("REFUTING " + Not(newPhi) + "...")
                solver.solveSAT(Not(newPhi)) match {
                  case (Some(true), invalidModel) =>
                    // Found as such as the xs break, refine predicates
                    predicates = valuateWithModelIn(phi, ass, invalidModel) +: predicates

                  case (Some(false), _) =>
                    result = Some(RuleSuccess(Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(satModel))).setType(tpe))))

                  case _ =>
                    continue = false
                    result = None
                }

              case (Some(false), _) =>
                if (predicates.isEmpty) {
                  result = Some(RuleSuccess(Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe))))
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

          result.getOrElse(RuleApplicationImpossible)
        }
      }
      List(res)
    } else {
      Nil
    }
  }
}
