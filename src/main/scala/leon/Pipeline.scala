package leon

abstract class Pipeline[-F, +T] {
  self =>

  def andThen[G](then: Pipeline[T, G]): Pipeline[F, G] = new Pipeline[F,G] {
    def run(ctx : LeonContext)(v : F) : G = then.run(ctx)(self.run(ctx)(v))
  }

  def run(ctx: LeonContext)(v: F): T
}
