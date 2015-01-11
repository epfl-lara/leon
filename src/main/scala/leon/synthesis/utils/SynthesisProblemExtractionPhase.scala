/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package utils

import purescala.Trees._
import purescala.TreeOps._
import purescala.Definitions._
import solvers.z3._
import solvers.Solver

object SynthesisProblemExtractionPhase extends LeonPhase[Program, (Program, Map[FunDef, Seq[ChooseInfo]])] {
  val name        = "Synthesis Problem Extraction"
  val description = "Synthesis Problem Extraction"

  def run(ctx: LeonContext)(p: Program): (Program, Map[FunDef, Seq[ChooseInfo]]) = {
    // Look for choose()
    val results = for (f <- p.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) yield {
      f -> ChooseInfo.extractFromFunction(p, f)
    }

    (p, results.toMap)
  }

}

