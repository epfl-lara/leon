/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import purescala.Definitions.Program

trait LeonPhase[-F, +T] extends Pipeline[F, T] with LeonComponent {
  // def run(ac: LeonContext)(v: F): T
}

trait SimpleLeonPhase[-F, +T] extends LeonPhase[F, T] {
  def apply(ctx: LeonContext, v: F): T

  def run(ctx: LeonContext, v: F): (LeonContext, T) = (ctx, apply(ctx, v))
}

abstract class TransformationPhase extends LeonPhase[Program, Program] {
  def apply(ctx: LeonContext, p: Program): Program

  override def run(ctx: LeonContext, p: Program) = {
    ctx.reporter.debug("Running transformation phase: " + name)(utils.DebugSectionLeon)
    (ctx, apply(ctx, p))
  }

}

abstract class UnitPhase[T] extends LeonPhase[T, T] {
  def apply(ctx: LeonContext, p: T): Unit

  override def run(ctx: LeonContext, p: T) = {
    ctx.reporter.debug("Running unit phase: " + name)(utils.DebugSectionLeon)
    apply(ctx, p)
    (ctx, p)
  }
}

case class NoopPhase[T]() extends LeonPhase[T, T] {
  val name = "noop"
  val description = "no-op"
  override def run(ctx: LeonContext, v: T) = (ctx, v)
}
