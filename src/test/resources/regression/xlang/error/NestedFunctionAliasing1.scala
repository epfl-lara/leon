import leon.lang._

object NestedFunctinAliasing1 {

  def f(): Int = {
    val a = Array(1,2,3,4)

    def g(b: Array[Int]): Unit = {
      require(b.length > 0 && a.length > 0)
      b(0) = 10
      a(0) = 17
    } ensuring(_ => b(0) == 10)

    g(a)
    a(0)
  } ensuring(_ == 10)
}
