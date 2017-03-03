import leon.lang._

object ParamsAliasing3 {

  case class A(var x: Int)

  def f1(a1: A, a2: A): Unit = {
    a1.x = a1.x + 1
    a1.x = a1.x + a2.x
  }

  def f(): Unit = {
    val a = A(10)
    f1(a, a) //cannot share data in scope of f1
    //leon would prove this valid if it doesn't reject the above
    //but it should be a.x == 22
    assert(a.x == 21)
  }

}
