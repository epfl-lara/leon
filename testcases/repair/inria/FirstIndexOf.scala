import leon.lang._
import leon.collection._
import leon.lang.synthesis._


object FirstIndexOf {
  def firstIndexOf(l: List[Int], v: Int): BigInt = {
    l match {
      case Cons(h, t) if v == h => BigInt(0)
      case Cons(h, t) =>
        if (firstIndexOf(t, v) >= 0) {
          firstIndexOf(t, v)+1
        } else {
          BigInt(-1)
        }
      case Nil() =>
        BigInt(-1)
    }
  } ensuring {
    (res: BigInt) => (if (l.content contains v) {
      l.size > res && l.apply(res) == v
    } else {
      res == -1
    }) && (((l,v), res) passes {
      case (Cons(0, Cons(1, Cons(2, Cons(3, Nil())))), 3) => 3
      case (Cons(0, Cons(2, Cons(3, Cons(1, Nil())))), 1) => 3
      case (Cons(0, Cons(1, Cons(3, Cons(1, Nil())))), 1) => 1
      case (Cons(0, Cons(1, Cons(3, Cons(1, Nil())))), 2) => -1
    })
  }
}
