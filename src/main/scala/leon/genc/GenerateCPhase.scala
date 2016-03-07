/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import purescala.Definitions.Program

object GenerateCPhase extends SimpleLeonPhase[Program, CAST.Prog] {

  val name = "Generate C"
  val description = "Generate equivalent C code from Leon's AST"

  def apply(ctx: LeonContext, program: Program) = {
    ctx.reporter.debug("Running code conversion phase: " + name)(utils.DebugSectionLeon)
    val cprogram = new CConverter(ctx, program).convert
    cprogram
  }

}

