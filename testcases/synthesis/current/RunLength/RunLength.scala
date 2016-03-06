import leon.lang._
import leon.lang.synthesis._
import leon.annotation._
import leon.collection._

object RunLength {


  def decode[A](l: List[(BigInt, A)]): List[A] = {
    def fill[A](i: BigInt, a: A): List[A] = {
      if (i > 0) a :: fill(i - 1, a)
      else Nil[A]()
    }
    l match {
      case Nil() => Nil[A]()
      case Cons((i, x), xs) =>
        fill(i, x) ++ decode(xs)
    }
  }


  def legal[A](l: List[(BigInt, A)]): Boolean = l match {
    case Cons((i, x), tl) =>
      i > 0 && (tl match {
        case Cons((_, y), _) => x != y
        case _ => true
      }) && legal(tl)
    case _ => true
  }

  /*def unique[A](l1: List[A], l2: List[A]) => {
    require(encode(l1) == encode(l2))
    l1 == l2
  }.holds*/

  // Solvable with --manual=2,0,0,1,0,0,3,0,1,1,0,0,1,0,0,0,1,1,1
  def encode[A](l: List[A]): List[(BigInt, A)] = {
    // Solution
    /*l match {
      case Nil() => Nil[(BigInt, A)]()
      case Cons(x, xs) =>
        val rec = encode(xs)
        rec match {
          case Nil() =>
            Cons( (BigInt(1), x), Nil[(BigInt,A)]())
          case Cons( (recC, recEl), recTl) =>
            if (x == recEl) {
              Cons( (1+recC, x), recTl)
            } else {
              Cons( (BigInt(1), x), rec )
            }
        }
    }*/
    ???[List[(BigInt, A)]]
  } ensuring {
    (res: List[(BigInt, A)]) =>
      legal(res) && decode(res) == l
  }

}
