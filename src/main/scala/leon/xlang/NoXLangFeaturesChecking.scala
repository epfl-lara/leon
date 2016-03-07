/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package xlang

import purescala.ExprOps.collect
import purescala.Definitions._

import utils.Position

import xlang.Expressions._

object NoXLangFeaturesChecking extends UnitPhase[Program] {

  val name = "no-xlang"
  val description = "Ensure and enforce that no xlang features are used"

  override def apply(ctx: LeonContext, pgm: Program): Unit = {
    val errors = pgm.definedFunctions.flatMap(fd => collect[(Position, String)]{
      case (e: Block) =>
        Set((e.getPos, "Block expressions require xlang desugaring"))
      case (e: Assignment) =>
        Set((e.getPos, "Mutating variables requires xlang desugaring"))
      case (e: While) =>
        Set((e.getPos, "While expressions require xlang desugaring"))
      case (e: Epsilon) =>
        Set((e.getPos, "Usage of epsilons requires xlang desugaring"))
      case (e: EpsilonVariable) =>
        Set((e.getPos, "Usage of epsilons requires xlang desugaring"))
      case (e: LetVar) =>
        Set((e.getPos, "Mutable variables (e.g. 'var x' instead of 'val x') require xlang desugaring"))
      case (e: ArrayUpdate) =>
        Set((e.getPos, "In-place updates of arrays require xlang desugaring"))
      case _ =>
        Set()
    }(fd.fullBody))

    for ((p, msg) <- errors) {
      ctx.reporter.error(p, msg)
    }
  }

}

