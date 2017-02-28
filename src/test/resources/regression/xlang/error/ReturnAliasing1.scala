import leon.lang._

object ReturnAliasing1 {

  case class A(var x: Int)

  def f(a: A): A = a

}
