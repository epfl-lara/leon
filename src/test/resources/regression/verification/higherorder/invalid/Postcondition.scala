import leon.Utils._

object Postconditions {
  def failling_1(f: Int => Int) = {
    require(forall((a: Int) => a > 0 ==> f(a) > 0))
    f(10)
  } ensuring { res => forall((a: Int) => res > f(a)) }

  def failling_2(f: Int => Int, x: Int) = {
    require(x >= 0 && forall((a: Int) => a > 0 ==> f(a) < 0))
    x
  } ensuring { res => forall((a: Int) => res > f(a)) }

}
