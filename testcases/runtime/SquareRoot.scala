import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object SquareRoot {

  def isqrt(x : Int) : Int = {
    choose { (y : Int) =>
      y * y <= x && (y + 1) * (y + 1) >= x
    }
  }

  def isqrt2(x: Int): Int = {
    if ((x == 0)) {
      0
    } else {
      if ((x < 0)) {
        leon.lang.error[(Int)]("(((y * y) ≤ x) ∧ (((y + 1) * (y + 1)) ≥ x)) is UNSAT!")
      } else {
        (choose { (y: Int) =>
          (((y * y) <= x) && (((y + 1) * (y + 1)) >= x))
        })
      }
    }
  }

  @ignore
  def main(a: Array[String]) {
    isqrt2(42)
  }
}
