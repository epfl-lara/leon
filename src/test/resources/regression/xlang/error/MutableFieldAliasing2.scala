object MutableFieldAliasing2 {

  case class A(var x: BigInt)
  case class B(a: A)

  def foo(a: A, b: B): Unit = {
    a.x = 10
  }

  def test(): Unit = {
    val a = A(0)
    val b = B(a) //shouldn't be allowed, create a shared reference
    foo(a, b) //showcase the issue created by the above, foo get two objects that share some data
    assert(a.x == b.a.x) //Leon concludes this is INVALID, but due to reference this should be VALID
  }

}
