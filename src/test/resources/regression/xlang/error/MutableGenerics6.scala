import leon.lang._

object MutableGenerics6 {

  def f[A](a: A) = a

  def g[A: Mutable](a: A) = f(a)

}
