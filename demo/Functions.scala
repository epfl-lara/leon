import funcheck.Annotations._
import funcheck.Utils._

object Functions {
  def someFunction(f : Int => Int, a : Int) : Boolean = {
    f(a) != a + 5
  } holds

  def conditional(a : Int, f : Int => Int, h : Int => Int) : Boolean = {
    val g = if (a > 5) f else h
    (f(a) == 42 && h(a) == 42) || h(a + 1) == 43
  } holds

  def plus42(a : Int) : Int = a + 42

  def usesSpecFun(a : Int) : Boolean = {
    someFunction(plus42, a)
  }
}
