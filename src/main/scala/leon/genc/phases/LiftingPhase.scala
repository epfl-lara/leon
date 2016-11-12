/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package phases

import ir.IRs.{ NIR, LIR }
import ir.{ ClassLifter }

/*
 * This phase lifts class types to their top level class and add appropriate
 * AsA cast to make sure the output program works on the same inputs.
 *
 * This is done in order to use tagged union to represent classes in C.
 */
private[genc] object LiftingPhase extends TimedLeonPhase[NIR.ProgDef, LIR.ProgDef] {
  val name = "Lifter"
  val description = "Lift class types to their hierarchy top class"

  def getTimer(ctx: LeonContext) = ctx.timers.genc.get("NIR -> LIR")

  def apply(ctx: LeonContext, nprog: NIR.ProgDef): LIR.ProgDef = {
    val reporter = MiniReporter(ctx)
    import reporter._

    val lifter = new ClassLifter(ctx)
    val lprog = lifter(nprog)

    debugTree("RESUTING LIR PROGRAM", lprog)

    lprog
  }
}


