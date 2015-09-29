import leon.invariant._

object ConcatVariationsAbs {
  def genL(n: BigInt): BigInt = {
    require(n >= 0)
    if (n == 0)
      BigInt(2)
    else
      4 + genL(n - 1)
  } ensuring (res => tmpl((a, b) => res <= a * n + b))

  def append(l1: BigInt, l2: BigInt): BigInt = {
    require(l1 >= 0 && l2 >= 0)
    if (l1 == 0)
      BigInt(3)
    else
      append(l1 - 1, l2 + 1) + 5
  } ensuring (res => tmpl((a, b) => res <= a * l1 + b))

  def f_good(m: BigInt, n: BigInt): BigInt = {
    require(0 <= m && 0 <= n)
    if (m == 0) BigInt(2)
    else {
      val t1 = genL(n)
      val t2 = f_good(m - 1, n)
      val t3 = append(n, n * (m - 1))
      (t1 + t2 + t3 + 6)
    }

  } ensuring (res => tmpl((a, b, c, d) => res <= a * (n * m) + b * n + c * m + d))

  def f_worst(m: BigInt, n: BigInt): BigInt = {
    require(0 <= m && 0 <= n)
    if (m == 0) BigInt(2)
    else {
      val t1 = genL(n)
      val t2 = f_worst(m - 1, n)
      val t3 = append(n * (m - 1), n)
      (t1 + t2 + t3 + 6)
    }

  } ensuring (res => tmpl((a, c, d, e, f) => res <= a * ((n * m) * m) + c * (n * m) + d * n + e * m + f))
}
