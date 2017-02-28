/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package phases

import ir.IRs.{ LIR, RIR }
import ir.{ Referentiator }

/*
 * This phase identify which variable should be reference instead of value,
 * and make sure reference are dereferenced before being accessed.
 *
 * Add ReferenceType, Ref and Deref to the input CIR program.
 *
 * NOTE a ReferenceType(T) is basically a T* in C.
 */
private[genc] object ReferencingPhase extends TimedLeonPhase[LIR.ProgDef, RIR.ProgDef] {
  val name = "Referencer"
  val description = "Add 'referencing' to the input LIR program to produce a RIR program"

  def getTimer(ctx: LeonContext) = ctx.timers.genc.get("CIR -> RIR")

  def apply(ctx: LeonContext, lprog: LIR.ProgDef): RIR.ProgDef = {
    val reporter = MiniReporter(ctx)
    import reporter._

    val referencing = new Referentiator(ctx)
    val rprog = referencing(lprog)

    debugTree("RESUTING RIR PROGRAM", rprog)

    rprog
  }
}


