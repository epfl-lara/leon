import leon.annotation._
import leon.lang._

object Datatypes {

  sealed abstract class Foo[A]
  sealed abstract class Bar[C] extends Foo[C]
  case class Baz[B](underlying: B, rest: Baz[B]) extends Bar[B]
  case class FooNil[D]() extends Foo[D]

  def dest[B](baz1: Baz[B], baz2: Baz[B]) = {
    require(baz1 == baz2)
    baz1.underlying == baz2.underlying
  } holds

  def intro_dest[B](baz1: Baz[B], baz2: Baz[B], b1: B, b2: B) = {
    require(b1 == b2)
    val x1 = Baz(b1, baz1)
    val x2 = Baz(b2, baz2)
    x1.underlying == x2.underlying
  } holds

  def pm[A](foo: Foo[A]) = (foo match {
    case Baz(x, y) => true
    case FooNil() => true
  }) holds

  def pm2[A](foo: Foo[A]) = (foo match {
    case Baz(x, y) => true
    case z: FooNil[A] => true
  }) holds

  def pm3[A](int: BigInt) = (int match {
    case BigInt(0) => true
    case n => true
  }) holds

  def pm4[A](int: BigInt) = (int match {
    case BigInt(0) => true
    case n if false => true
    case n => true
  }) holds

}
