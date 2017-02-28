/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package phases

import ir.IRs.{ CIR, NIR }
import ir.{ Normaliser }

/*
 * Normalise the program by adding explicit execution points and making sure
 * argument-like expressions are "simple" expressions (and not e.g. blocks).
 */
private[genc] object NormalisationPhase extends TimedLeonPhase[CIR.ProgDef, NIR.ProgDef] {
  val name = "Normaliser"
  val description = "Normalise IR to match the C execution model"

  def getTimer(ctx: LeonContext) = ctx.timers.genc.get("CIR -> NIR")

  def apply(ctx: LeonContext, cprog: CIR.ProgDef): NIR.ProgDef = {
    val reporter = MiniReporter(ctx)
    import reporter._

    val normaliser = new Normaliser(ctx)
    val nprog = normaliser(cprog)

    debugTree("RESUTING NIR PROGRAM", nprog)

    nprog
  }
}


