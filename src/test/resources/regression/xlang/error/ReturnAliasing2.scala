import leon.lang._

object ReturnAliasing2 {

  case class A(var x: Int)
  case class W(a: A)

  def f(a: A): W = W(a)

}
