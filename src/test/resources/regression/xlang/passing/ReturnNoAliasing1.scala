import leon.lang._

object ReturnNoAliasing1 {

  case class A(var x: Int)

  def f(y: Int): A = A(y)

}
