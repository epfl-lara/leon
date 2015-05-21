import leon.lang.invariantLang._

object Seive {
  sealed abstract class L
  case class C(h: (Int, Boolean), t: L) extends L
  case object N extends L

  def size(l: L): Int = {
    l match {
      case N => 0
      case C(_, t) => 1 + size(t)
    }
  }

  def isCancelled(n: Int, l: L): Boolean = {
    //require(n <= size(l))
    l match {
      case N => false
      case C((a, c), t) => {
        if (a == n) c
        else isCancelled(n, t)
      }
    }
  } ensuring(res => true template((a, b) => time <= a * size(l) + b))

  def genListHelper(n: Int, curr: Int): L = {
    if(n > curr) N
    else C((curr, false), genListHelper(n, curr + 1))
  } ensuring(res => true template((a, b) => time <= a * (n - curr) + b))

  def genList(n: Int): L = {
    genListHelper(n, 1)
  } ensuring(res => true template((a, b) => time <= a * n + b))

  def cancelMultiples(p: Int, l: L): L = {
    l match {
      case N => N
      case C((n, b), t) =>
        if ((n / p) * p == n) C((n, b), cancelMultiples(p, t))
        else C((n, true), cancelMultiples(p, t))
    }
  } ensuring(res => true template((a, b) => time <= a * size(l) + b))

  def removeComposite(l: L): L = {
    l match {
      case N => N
      case C((a, c), t) if (c) => C((a, c), removeComposite(t))
      case C(_, t) => removeComposite(t)
    }
  } ensuring(res => true template((a, b) => time <= a * size(l) + b))

  def seiveHelper(l: L, n: Int, curr: Int): L = {
    if (curr > n) l
    else {
      if (isCancelled(curr, l)) {
        seiveHelper(l, n, curr + 1)
      }
      else {
        val cl = cancelMultiples(curr, l)
        seiveHelper(cl, n, curr + 1)
      }
    }
  } ensuring(res => true template((a, b, c, d) => time <= a*(size(l)*n) + b*n + c*size(l) + d))
  // } ensuring(res => time <= 100*(size(l)*n) + 100*n + 10)

  def seive(n: Int): L = {
    val il = genList(n)
    val sl = seiveHelper(il, n, 2)
    removeComposite(sl)
  }
}