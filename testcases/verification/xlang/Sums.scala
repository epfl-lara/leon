import leon.lang._

object Sums {

  def summ(to : BigInt): BigInt = ({
    require(to >= 0)
    var i: BigInt = 0
    var s: BigInt = 0
    (while (i < to) {
      s = s + i
      i = i + 1
    }) invariant (s >= 0 && i >= 0 && s == i*(i-1)/2 && i <= to)
    s
  }) ensuring(res => res >= 0 && res == to*(to-1)/2)


  def sumsq(to : BigInt): BigInt = ({
    require(to >= 0)
    var i: BigInt = 0
    var s: BigInt = 0
    (while (i < to) {
      s = s + i*i
      i = i + 1
    }) invariant (s >= 0 && i >= 0 && s == (i-1)*i*(2*i-1)/6 && i <= to)
    s
  }) ensuring(res => res >= 0 && res == (to-1)*to*(2*to-1)/6)

}
