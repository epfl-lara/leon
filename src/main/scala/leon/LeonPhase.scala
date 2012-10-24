package leon

import purescala.Definitions.Program

abstract class LeonPhase[F, T] {
  val name: String
  val description: String

  def definedOptions: Set[LeonOptionDef] = Set()

  def run(ac: LeonContext)(v: F): T
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

case class ExitPhase[T]() extends LeonPhase[T, Unit] {
  val name = "end";
  val description = "end"
  override def run(ctx: LeonContext)(v: T) = ()
}
