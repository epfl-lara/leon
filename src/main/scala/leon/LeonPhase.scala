/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import purescala.Definitions.Program

trait LeonPhase[-F, +T] extends Pipeline[F, T] with LeonComponent {
  // def run(ac: LeonContext)(v: F): T
}

abstract class TransformationPhase extends LeonPhase[Program, Program] {
  def apply(ctx: LeonContext, p: Program): Program

  override def run(ctx: LeonContext)(p: Program) = {
    apply(ctx, p)
  }
}

abstract class UnitPhase[Program] extends LeonPhase[Program, Program] {
  def apply(ctx: LeonContext, p: Program): Unit

  override def run(ctx: LeonContext)(p: Program) = {
    apply(ctx, p)
    p
  }
}

case class NoopPhase[T]() extends LeonPhase[T, T] {
  val name = "noop";
  val description = "no-op"
  override def run(ctx: LeonContext)(v: T) = v
}
