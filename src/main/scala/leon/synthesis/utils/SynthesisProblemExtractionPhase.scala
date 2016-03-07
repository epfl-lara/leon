/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package utils

import purescala.DefOps.funDefsFromMain
import purescala.Definitions._

object SynthesisProblemExtractionPhase extends SimpleLeonPhase[Program, (Program, Map[FunDef, Seq[SourceInfo]])] {
  val name        = "Synthesis Problem Extraction"
  val description = "Synthesis Problem Extraction"

  def apply(ctx: LeonContext, p: Program): (Program, Map[FunDef, Seq[SourceInfo]]) = {
    // Look for choose()
    val results = for (f <- funDefsFromMain(p).toSeq.sortBy(_.id) if f.body.isDefined) yield {
      f -> SourceInfo.extractFromFunction(ctx, p, f)
    }

    (p, results.toMap)
  }

}

