/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package utils

import purescala.Trees._
import purescala.TreeOps._
import purescala.Definitions._
import solvers.z3._
import solvers.Solver

object SynthesisProblemExtractionPhase extends LeonPhase[Program, (Program, Map[FunDef, Seq[Problem]])] {
  val name        = "Synthesis Problem Extraction"
  val description = "Synthesis Problem Extraction"

  def run(ctx: LeonContext)(p: Program): (Program, Map[FunDef, Seq[Problem]]) = {
    var results  = Map[FunDef, Seq[Problem]]()
    def noop(u:Expr, u2: Expr) = u


    def actOnChoose(f: FunDef)(e: Expr, a: Expr): Expr = e match {
      case ch @ Choose(vars, pred) =>
        val problem = Problem.fromChoose(ch)

        results += f -> (results.getOrElse(f, Seq()) :+ problem)

        a
      case _ =>
        a
    }

    // Look for choose()
    for (f <- p.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) {
      treeCatamorphism(x => x, noop, actOnChoose(f), f.body.get)
    }

    (p, results)
  }

}

