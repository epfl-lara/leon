import leon.invariant._
import leon.instrumentation._


object ConcatVariations {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  def size(l: List): BigInt = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  })

  def genL(n: BigInt): List = {
    require(n >= 0)
    if (n == 0) Nil()
    else
      Cons(n, genL(n - 1))
  } ensuring (res => size(res) == n && tmpl((a,b) => time <= a*n + b))

  def append(l1: List, l2: List): List = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => Cons(x, append(xs, l2))

  }) ensuring (res =>  size(l1) + size(l2) == size(res) && tmpl((a,b) => time <= a*size(l1) + b))

  def f_good(m: BigInt, n: BigInt): List = {
    require(0 <= m && 0 <= n)
    if (m == 0) Nil()
    else append(genL(n), f_good(m - 1, n))

  } ensuring(res => size(res) == n*m && tmpl((a,b,c,d) => time <= a*(n*m) + b*n + c*m +d))

  def f_worst(m: BigInt, n: BigInt): List = {
    require(0 <= m && 0 <= n)

    if (m == 0) Nil()
    else append(f_worst(m - 1, n), genL(n))

  } ensuring(res => size(res) == n*m && tmpl((a,c,d,e,f) => time <= a*((n*m)*m)+c*(n*m)+d*n+e*m+f))
}
