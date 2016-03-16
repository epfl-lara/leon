import leon.lang._

object ObjectAliasing1 {

  case class A(var x: Int)

  def f1(): Int = {
    val a = A(10)
    val b = a
    b.x = 15
    a.x
  } ensuring(_ == 15)

}

