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
  } ensuring { res =>
    (a, res) passes {
      case 0  => 0
      case 1  => 1
      case 2  => 1
      case 3  => 2
      case 4  => 3
      case 5  => 5
      case 18 => 2584
    }
  }



}
