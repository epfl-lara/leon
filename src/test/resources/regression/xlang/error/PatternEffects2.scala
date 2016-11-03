import leon.lang._

import PatternEffects2._

object PatternEffects2FooA {
  def unapply(a: A): Option[Int] = {
    update(a)
    if(a.x > 10) Some(a.x) else None[Int]
  }
}

object PatternEffects2 {
  case class A(var x: Int)


  def update(b: A): Boolean = {
    b.x = b.x + 1
    b.x > 0
  }

  def foo(a: A): Int = (a match {
    case PatternEffects2FooA(x) => x
    case A(x) => 20
  }) ensuring(res => res > 10)

}
