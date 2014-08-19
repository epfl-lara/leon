import leon.lang._
import leon.lang.synthesis._

object Math {

  def fib(a: Int): Int = {
    require(a >= 0)
    if (a > 1) {
      fib(a-1) + fib(a-2)
    } else {
      ???[Int]
    }
  } ensuring {
    passes(a, _)(Map(
      0 -> 0,
      1 -> 1,
      2 -> 1,
      3 -> 2,
      4 -> 3,
      5 -> 5,
      18 -> 2584
    ))
  }

  def abs(a: Int): Int = {
    if (?(a >= 0, a <= 0, a == 0, a != 0)) {
      a
    } else {
      -a
    }
  } ensuring { _ >= 0 }



}
