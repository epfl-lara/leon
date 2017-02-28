import leon.lang._

object ParamsAliasing1 {

  case class A(var x: Int)

  def f1(a1: A, a2: A): Int = {
    a2.x = a1.x
    a1.x = 0
    a2.x
  } ensuring(res => a1.x + a2.x == res && a2.x == old(a1).x)

  def f(): Int = {
    val a = A(10)
    f1(a, a) //cannot share data in scope of f1
  }

}
