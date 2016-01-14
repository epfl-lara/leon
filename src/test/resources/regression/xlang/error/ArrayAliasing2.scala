import leon.lang._

object ArrayAliasing2 {

  def f1(a: Array[BigInt]): BigInt = {
    val b = a
    b(0) = 10
    a(0)
  } ensuring(_ == 10)

}
