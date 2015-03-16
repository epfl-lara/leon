/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package utils

import purescala.Definitions._

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

