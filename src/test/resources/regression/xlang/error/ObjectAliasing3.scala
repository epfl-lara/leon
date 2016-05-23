import leon.lang._

object ObjectAliasing3 {

  case class A(var x: Int)

  def f1(a: A, b: Boolean): Int = {
    val c = if(b) a else A(42)
    c.x = 10
    a.x
  } ensuring(_ == 10)

}
