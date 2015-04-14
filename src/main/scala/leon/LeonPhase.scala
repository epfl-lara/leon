/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import purescala.Definitions.Program

trait LeonPhase[-F, +T] extends Pipeline[F, T] with LeonComponent {

  // def run(ac: LeonContext)(v: F): T
}

abstract class TransformationPhase extends LeonPhase[Program, Program] {
  def apply(ctx: LeonContext, p: Program): Program

  override def run(ctx: LeonContext)(p: Program) = {
    ctx.reporter.debug("Running transformation phase: " + name)(utils.DebugSectionLeon)
    apply(ctx, p)
  }
}

abstract class UnitPhase[T] extends LeonPhase[T, T] {
  def apply(ctx: LeonContext, p: T): Unit

  override def run(ctx: LeonContext)(p: T) = {
    ctx.reporter.debug("Running unit phase phase: " + name)(utils.DebugSectionLeon)
    apply(ctx, p)
    p
  }
}

case class NoopPhase[T]() extends LeonPhase[T, T] {
  val name = "noop"
  val description = "no-op"
  override def run(ctx: LeonContext)(v: T) = v
}
