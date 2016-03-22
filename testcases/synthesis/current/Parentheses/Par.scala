import leon.lang._
import leon.lang.synthesis._
import leon.collection._


object MatchPar {
  abstract class AbsChar
  case object OP extends AbsChar
  case object CP extends AbsChar
  case object NA extends AbsChar

  def matchPar(l: List[AbsChar]): BigInt = {

    ???[BigInt]
    /*
    l match {
      case Nil() => 0
      case Cons(h, t) =>
        val rec = matchPar(t)
        h match {
          case OP => 1 + rec
          case CP => if (rec <= 0) {
            -1
          } else {
            rec - 1
          }
          case NA => rec
        }
    }*/
  } ensuring { res =>
    ((count(OP, l) != count(CP, l)) ==> (res != 0)) &&
    ((l, res) passes {
      case Nil() => 0
      case Cons(OP, Cons(CP, Nil())) => 0
      case Cons(CP, Cons(OP, _))     => -1
      case Cons(OP, Cons(OP, Nil())) => 2
      case Cons(OP, Cons(OP, Cons(CP, Cons(CP, Cons(OP, Cons(CP, Nil())))))) => 0
    })
  }

  def count[T](a: T, l: List[T]): BigInt = {
    l match {
      case Cons(h, t) =>
        if (h == a) {
          1 + count(a, t)
        } else {
          count(a, t)
        }
      case Nil() => BigInt(0)
    }
  } ensuring { (res: BigInt) =>
    res >= 0
  }
}
