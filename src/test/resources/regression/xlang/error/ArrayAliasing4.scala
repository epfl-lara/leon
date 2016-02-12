import leon.lang._

object ArrayAliasing4 {

  def f1(a: Array[BigInt]): Array[BigInt] = {
    require(a.length > 0)
    a(0) = 10
    a
  } ensuring(res => res(0) == 10)

}
