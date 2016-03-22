import leon.lang._

object ObjectAliasing5 {

  case class A(var x: Int)
  case class B(a: A)

  def f1(b: B): A = {
    b.a
  }

}
