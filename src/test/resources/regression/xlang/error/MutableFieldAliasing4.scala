object MutableFieldAliasing4 {

  case class A(var x: BigInt)
  case class B(a: A, f: (A) => BigInt)

  def foo(a: A, b: B): Unit = {
    a.x = 10
  }

  def test(): Unit = {
    val a = A(0)
    val b = B(a, (x: A) => { x.x += 1; x.x })
    foo(a, b)
    assert(a.x == b.a.x)
  }

}
