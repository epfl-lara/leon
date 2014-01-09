import leon.Utils._

object Simple {

  def passing_1(f: Int => Int) = {
    require(forall((a: Int) => a > 0 ==> f(a) > 0))
    f(10)
  } ensuring { res => res > 0 }

  def passing_2(f: Int => Int) = {
    require(forall((a: Int) => a > 0 ==> f(a) > 1))
    f(1) + f(2)
  } ensuring { res => res > 2 }

  def passing_3(f: Int => Int) = {
    require(forall((a: Int) => f(a) > 0 || f(a) < 0))
    f(8)
  } ensuring { res => res != 0 }

  def passing_4(f: Int => Int, g: Int => Int, x: Int) = {
    require(forall((a: Int, b: Int) => f(a) + g(b) > 0))
    if(x <= 0) f(x) + g(x)
    else x
  } ensuring { res => res > 0 }

  def passing_5(f: Int => Int, g: Int => Boolean) = {
    require(forall((a: Int) => if(g(a)) { f(a) > 0 || f(a) < 0 } else { f(a) == 0 }))
    if(g(8)) f(8)
    else 1
  } ensuring { res => res != 0 }

  def passing_6(f: Int => Int, x: Int) = {
    require(x > 0 && forall((a: Int) => a > 0 ==> f(a) > 0))
    if(x > 0) f(1)
    else f(-1)
  } ensuring { res => res > 0 }

  def passing_7(f: Int => Int) = {
    require(forall((a: Int) => a > 0 ==> f(a) > 0))
    val a = f(-1)
    f(2)
  } ensuring { res => res > 0 }

}
