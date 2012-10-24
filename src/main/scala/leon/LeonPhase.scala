package leon

import purescala.Definitions.Program

abstract class LeonPhase {
  val name: String
  val description: String

  def run(ac: LeonContext): LeonContext
}

abstract class TransformationPhase extends LeonPhase {
  def apply(p: Program): Program

  override def run(ctx: LeonContext) = {
    ctx.program match {
      case Some(p) =>
        ctx.copy(program = Some(apply(p)))
      case None =>
        ctx.reporter.fatalError("Empty program at this point?!?")
        ctx
    }
  }
}

abstract class UnitPhase extends LeonPhase {
  def apply(p: Program): Unit

  override def run(ctx: LeonContext) = { 
    ctx.program match {
      case Some(p) =>
        apply(p)
      case None =>
        ctx.reporter.fatalError("Empty program at this point?!?")
    }
    ctx
  }
}
