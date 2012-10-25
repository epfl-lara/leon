package leon

abstract class Pipeline[F, T] {
  def andThen[G](then: LeonPhase[T, G]): Pipeline[F, G];
  def followedBy[G](pipe: Pipeline[T, G]): Pipeline[F, G];
  def run(ctx: LeonContext)(v: F): T;
}

class PipeCons[F, V, T](phase: LeonPhase[F, V], then: Pipeline[V, T]) extends Pipeline[F, T] {
  def andThen[G](last: LeonPhase[T, G]) = new PipeCons(phase, then andThen last)
  def followedBy[G](pipe: Pipeline[T, G]) = new PipeCons(phase, then followedBy pipe);
  def run(ctx: LeonContext)(v: F): T = then.run(ctx)(phase.run(ctx)(v))

  override def toString = {
    phase.toString + " -> " + then.toString
  }
}

class PipeNil[T]() extends Pipeline[T,T] {
  def andThen[G](last: LeonPhase[T, G]) = new PipeCons(last, new PipeNil)
  def run(ctx: LeonContext)(v: T): T = v
  def followedBy[G](pipe: Pipeline[T, G]) = pipe;
  override def toString = {
    "|"
  }
}
