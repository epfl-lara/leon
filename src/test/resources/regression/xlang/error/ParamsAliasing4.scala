import leon.lang._

object ParamsAliasing4 {

  case class A(var x: Int)
  case class B(a1: A, a2: A)

  def f1(a1: A, a2: A): Unit = {
    a1.x = a1.x + 1
    a2.x = a2.x + 1
  }

  def f(): Unit = {
    val b = B(A(10), A(15))
    //in theory, this should be fine, but the implementation is not able to reconstruct B properly so we reject
    f1(b.a1, b.a2)
    assert(b.a1.x + b.a2.x == 27)
  }

}
