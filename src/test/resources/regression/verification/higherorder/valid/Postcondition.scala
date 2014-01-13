import leon.Utils._

object Postconditions {

  def passing_1(f: Int => Int, x: Int) = {
    require(x >= 0 && forall((a: Int) => f(a) < 0))
    x
  } ensuring { res => forall((a: Int) => res > f(a)) }

  def passing_2(f: Int => Int, x: Int) = {
    require(x >= 0 && forall((a: Int) => a > 0 ==> f(a) < 0))
    x
  } ensuring { res => forall((a: Int) => a > 0 ==> res > f(a)) }

  def passing_3(f: Int => Int) = {
    require(forall((a: Int) => f(a) > 0))
    f
  } ensuring { res => forall((a: Int) => res(a) > 0) }

  def passing_4() = {
    (x: Int) => x + 1
  } ensuring { res => forall((a: Int) => res(a) > a) }
}
