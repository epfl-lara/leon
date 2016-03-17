import leon.lang._

object ObjectAliasing4 {

  case class A(var x: Int)

  def f1(a: A): A = {
    a.x = 10
    a
  } ensuring(res => res.x == 10)

}
