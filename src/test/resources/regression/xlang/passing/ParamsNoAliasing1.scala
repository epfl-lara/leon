import leon.lang._

object ParamsNoAliasing1 {

  case class A(var x: Int)
  case class B(a: A, lit: Int)

  def f1(a: A, lit: Int): Unit = {
    a.x = a.x + 1
  }

  def f(): Unit = {
    val b = B(A(10), 15)
    f1(b.a, b.lit)
    assert(b.a.x + b.lit == 26)
  }

}
