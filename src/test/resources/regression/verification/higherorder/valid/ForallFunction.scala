import leon.Utils._

object Testing {
  def passing_1(f: (Int => Int) => Int): Int = {
    require(forall((g: Int => Int, a: Int) => g(a) >= 0 ==> f(g) >= 0))
    val lambda = (x: Int) => if (x < 0) -x else x
    f(lambda)
  } ensuring { _ >= 0 }
}

// vim: set ts=4 sw=4 et:
