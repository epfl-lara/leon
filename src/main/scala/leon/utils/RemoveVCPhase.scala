/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

import leon.{ LeonContext, TransformationPhase }
import leon.purescala.Definitions.{ ClassDef, FunDef, Program }
import leon.purescala.DefOps.{ definitionReplacer, transformProgram }
import leon.purescala.Expressions.{ Assert, Ensuring, Expr, Require }
import leon.purescala.ExprOps.{ preMap }

/*
 * This phase removes all verification condition it can find in the given
 * program, without mutating it!
 *
 * NOTE This phase expects methods to have been lifted first.
 */
object RemoveVCPhase extends TransformationPhase {

  val name = "Remove verification conditions"
  val description = "Remove assertions, loop invariant pre & postconditions"

  def apply(ctx: LeonContext, p: Program): Program = {
    ctx.reporter.debug("Running VC removal phase")(leon.utils.DebugSectionLeon)
    val timer = ctx.timers.removeVC.start()

    val res = transformProgram(transformer, p)

    timer.stop()
    res
  }

  // This transformer will replace function definitions and their invocations with a new
  // version without VC.
  private lazy val transformer = definitionReplacer(funMapper, noClassMapper)

  private def funMapper(fd: FunDef): Option[FunDef] = Some(funMapperImpl(fd))

  private def funMapperImpl(fd: FunDef): FunDef = {
    val newFd = fd.duplicate()
    newFd.fullBody = preMap(exprMapper, applyRec = true)(newFd.fullBody)
    newFd
  }

  // Actually removed VC expressions
  private def exprMapper(expr: Expr): Option[Expr] = expr match {
    case Require(_, body) => Some(body)
    case Ensuring(body, _) => Some(body)
    case Assert(_, _, body) => Some(body)
    case _ => None
  }

  // Because we assume methods were lifted from classes, we don't need to procees them.
  private def noClassMapper(cd: ClassDef): Option[ClassDef] = None
}

