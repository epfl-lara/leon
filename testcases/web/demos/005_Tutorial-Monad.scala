import leon.lang.string._
import leon.annotation._

sealed abstract class Outcome[T] {
  def map[S](f: T => S): Outcome[S] = {
    this match {
      case ReturnOK(v) => ReturnOK[S](f(v))
      case Throw(msg) => Throw[S](msg)
    }
  }
  def flatMap[S](f: T => Outcome[S]): Outcome[S] = {
    this match {
      case ReturnOK(v) => f(v)
      case Throw(msg) => Throw[S](msg)
    }
  }

}
case class ReturnOK[T](v: T) extends Outcome[T]
case class Throw[T](msg: String) extends Outcome[T]

object Test { 
  def test : Outcome[BigInt] = {
    val c1 = ReturnOK[BigInt](32)
    val c2 = ReturnOK[BigInt](20)
    for (v1 <- c1; v2 <- c2) 
      yield (v1 + v2)
  }
  def foo : BigInt = test match {
    case ReturnOK(v) => v
    case _ => 0
  }
  
  def associative_lemma[T,U,V](m: Outcome[T], f: T => Outcome[U], g: U => Outcome[V]): Boolean = {
    m.flatMap(f).flatMap(g) == m.flatMap((x:T) => f(x).flatMap(g))
  }
  
  def associative_lemma_for[T,U,V](m: Outcome[T], f: T => Outcome[U], g: U => Outcome[V]): Boolean = {
    (for (x <- m; y <- f(x); z <- g(y)) yield z) ==
    (for (y1 <- (for (x <- m; y <- f(x)) yield y); z <- g(y1)) yield z) &&
    (for (x <- m; y <- f(x); z <- g(y)) yield z) ==
    (for (x <- m; z1 <- (for (y <- f(x); z <- g(y)) yield z)) yield z1)
  }
}
