object ArrayInitialization3 {

  case class A(var x: BigInt)

  def foo(a: A): Unit = {
    a.x = 10
  }

  def test(): Unit = {
    val a = A(0)
    val t = Array.fill(10)(a)
    foo(a)
    assert(t(0).x == a.x)
  }


}
