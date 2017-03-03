import leon.lang._

object ReturnAliasing4 {

  case class A(var x: Int)

  def f(a: A, b: Boolean): A = if(b) A(10) else a

}
