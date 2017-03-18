import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._
import leon.grammar.Grammar._

object StrictSortedListInsert {

  def size(l: List[BigInt]): BigInt = (l match {
    case Nil() => BigInt(0)
    case Cons(_, t) => BigInt(1) + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List[BigInt]): Set[BigInt] = l match {
    case Nil() => Set.empty[BigInt]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def isSorted(list: List[BigInt]): Boolean = list match {
    case Nil() => true
    case Cons(_, Nil()) => true
    case Cons(x1, Cons(x2, _)) if(x1 >= x2) => false
    case Cons(_, xs) => isSorted(xs)
  }

  def indexOf(list: List[BigInt], elem: BigInt): BigInt = {
    require(isSorted(list))
    ???[BigInt]
  } ensuring { res =>
    ((list, elem), res) passes {
      case (Nil(), _) => 0
      case (Cons(x1, _), y) if y < x1 => 0
      case (Cons(x1, Cons(x2, _)), y) if x1 <= y && y < x2 => 1
      case (Cons(x1, Cons(x2, Cons(x3, _))), y) if x2 <= y && y < x3 => 2
    }
  }
  
}
