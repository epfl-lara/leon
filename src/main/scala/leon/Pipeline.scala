/* Copyright 2009-2015 EPFL, Lausanne */

package leon

abstract class Pipeline[-F, +T] {
  self =>

  def andThen[G](thenn: Pipeline[T, G]): Pipeline[F, G] = new Pipeline[F,G] {
    def run(ctx : LeonContext)(v : F) : G = {
      val s = self.run(ctx)(v)
      if(ctx.settings.terminateAfterEachPhase) ctx.reporter.terminateIfError()
      thenn.run(ctx)(s)
    }
  }

  def run(ctx: LeonContext)(v: F): T
}
