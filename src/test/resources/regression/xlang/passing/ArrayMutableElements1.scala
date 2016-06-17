object ArrayMutableElements1 {

  case class A(var x: BigInt)

  def foo(table: Array[A], a: A): Unit = {
    a.x = 10
  }

  def test(): Unit = {
    val a = A(0)
    val t = Array(A(0), A(0), A(0))
    foo(t, a)
    assert(t(0).x != a.x)
  }


}
