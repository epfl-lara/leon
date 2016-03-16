import leon.lang._

object ObjectAliasing2 {

  case class A(var x: Int)

  def f1(a: A): Int = {
    val b = a
    b.x = 10
    a.x
  } ensuring(_ == 10)

}
