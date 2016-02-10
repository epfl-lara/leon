import leon.lang._

object ArrayAliasing3 {

  def f1(a: Array[BigInt], b: Boolean): BigInt = {
    val c = if(b) a else Array[BigInt](1,2,3,4,5)
    c(0) = 10
    a(0)
  } ensuring(_ == 10)

}
