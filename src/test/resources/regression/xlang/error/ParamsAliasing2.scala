import leon.lang._

object ParamsAliasing2 {

  case class A(var x: Int)

  def f(f1: (A, A) => Int): Int = {
    val a = A(10)
    f1(a, a) //cannot share data in scope of f1
  }

}
