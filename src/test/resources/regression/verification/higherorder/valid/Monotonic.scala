import leon.Utils._

object Monotonic {
  def composeMonotonic(f: Int => Int, g: Int => Int): Int => Int = {
    require(forall((a: Int, b: Int) => (a > b ==> f(a) > f(b)) && (a > b ==> g(a) > g(b))))
    (x: Int) => f(g(x))
  } ensuring { res => forall((a: Int, b: Int) => a > b ==> res(a) > res(b)) }
}

// vim: set ts=4 sw=4 et:
