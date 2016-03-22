import leon.lang._

object ObjectAliasing6 {

  case class A(var x: Int)
  case class B(a: A)

  def f1(b: B): Int = {
    val a = b.a
    a.x = 12
    b.a.x
  } ensuring(_ == 12)

}
