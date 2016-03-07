import leon.lang._

object ArrayAliasing5 {


  def f1(a: Array[BigInt], b: Array[BigInt]): Unit = {
    require(a.length > 0 && b.length > 0)
    a(0) = 10
    b(0) = 20
  } ensuring(_ => a(0) == 10 && b(0) == 20)


  def callWithAliases(): Unit = {
    val a = Array[BigInt](0,0,0,0)
    f1(a, a)
  }

}
