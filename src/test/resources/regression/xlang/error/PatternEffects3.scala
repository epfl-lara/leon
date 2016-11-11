import leon.lang._

import PatternEffects3._

object PatternEffects3FooA {
  def unapply(a: A): Option[Int] = {
    update(a)
    if(a.x > 10) Some(a.x) else None[Int]
  }
}

object PatternEffects3 {

  case class A(var x: Int)
  case class B(a: A)

  def update(b: A): Boolean = {
    b.x = b.x + 1
    b.x > 0
  }

  def foo(b: B): Int = (b match {
    case B(PatternEffects3FooA(x)) => x
    case B(A(x)) => 20
  }) ensuring(res => res > 10)

}
