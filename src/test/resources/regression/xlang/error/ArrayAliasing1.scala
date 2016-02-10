import leon.lang._

object ArrayAliasing1 {

  def f1(): BigInt = {
    val a = Array.fill(10)(BigInt(0))
    val b = a
    b(0) = 10
    a(0)
  } ensuring(_ == 10)

}

