import leon.Utils._

object Simple {

  def failling_1(f: Int => Int) = {
    require(forall((a: Int) => a > 0 ==> f(a) > 0))
    f(-1)
  } ensuring { res => res > 0 }

  def failling_2(f: Int => Int) = {
    require(forall((a: Int) => a > 0 ==> f(a) > 1))
    f(1) + f(2)
  } ensuring { res => res > 4 }

  def failling_4(f: Int => Int, g: Int => Int, x: Int) = {
    require(forall((a: Int, b: Int) => f(a) + g(b) > 0))
    if(x < 0) f(x) + g(x)
    else x
  } ensuring { res => res > 0 }
}
