/* Copyright 2009-2013 EPFL, Lausanne */

package leon

abstract class Pipeline[-F, +T] {
  self =>

  def andThen[G](thenn: Pipeline[T, G]): Pipeline[F, G] = new Pipeline[F,G] {
    def run(ctx : LeonContext)(v : F) : G = thenn.run(ctx)(self.run(ctx)(v))
  }

  def run(ctx: LeonContext)(v: F): T
}
