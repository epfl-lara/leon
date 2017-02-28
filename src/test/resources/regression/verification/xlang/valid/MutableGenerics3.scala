import leon.lang._

object MutableGenerics3 {

  case class C(var x: Int)

  def f[A: Mutable](a: A, h: (A) => Unit) = h(a)

  def g[A: Mutable](a: A, h: (A) => Unit) = f(a, h)

  def test(): Unit = {
    val c = C(42)
    g(c, (c2: C) => c2.x += 1)
    assert(c.x == 43)
  }

}
