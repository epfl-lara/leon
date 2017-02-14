import leon.lang._

object ReturnAliasing3 {

  case class A(var x: Int)

  def f(a: A): Array[A] = Array(a)

}
