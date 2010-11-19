import scala.collection.immutable.Set
import funcheck.Annotations._
import funcheck.Utils._

object ListWithSize {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    // proved with unrolling=0
    def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) ensuring(_ >= 0)

    def size2(l: List) : Int = size2acc(l, 0)
    def size2acc(l: List, acc: Int) : Int = {
     require(acc >= 0)
     l match {
       case Nil() => acc
       case Cons(_, xs) => size2acc(xs, acc+1)
     }
    } ensuring(res => res == size(l) + acc)

    def sizesAreEquiv(l: List) : Boolean = {
      size(l) == size2(l)
    } holds

    def content(l: List) : Set[Int] = l match {
      case Nil() => Set.empty[Int]
      case Cons(x, xs) => Set(x) ++ content(xs)
    }

    def sizeAndContent(l: List) : Boolean = {
      size(l) == 0 || content(l) != Set.empty[Int]
    } ensuring(_ == true)

    def drunk(l : List) : List = (l match {
      case Nil() => Nil()
      case Cons(x,l1) => Cons(x,Cons(x,drunk(l1)))
    }) ensuring (size(_) == 2 * size(l))

    // proved with unrolling=1
    def funnyCons(x: Int, l: List) : List = (l match {
        case Nil() => Cons(x, Nil())
        case c @ Cons(_,_) => Cons(x, c)
    }) ensuring(size(_) > 0)

    // proved with unrolling=2
    def reverse(l: List) : List = reverse0(l, Nil()) ensuring(content(_) == content(l))
    def reverse0(l1: List, l2: List) : List = (l1 match {
      case Nil() => l2
      case Cons(x, xs) => reverse0(xs, Cons(x, l2))
    }) ensuring(content(_) == content(l1) ++ content(l2))

    def append(l1 : List, l2 : List) : List = (l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, append(xs, l2))
    })

    @induct
    def nilAppend(l : List) : Boolean = (append(l, Nil()) == l) holds

    // unclear if we needed this--it was meant to force folding
    def appendFold(x : Int, xs : List, ys : List) : Boolean = {
      true
    } ensuring (res => res && Cons(x,append(xs, ys)) == append(Cons(x,xs), ys))

    @induct
    def appendAssoc(xs : List, ys : List, zs : List) : Boolean =
      (append(append(xs, ys), zs) == append(xs, append(ys, zs))) holds

    @induct
    def sizeAppend(l1 : List, l2 : List) : Boolean =
      (size(append(l1, l2)) == size(l1) + size(l2)) holds

    // proved with unrolling=4
    @induct
    def concat(l1: List, l2: List) : List = 
      concat0(l1, l2, Nil()) ensuring(content(_) == content(l1) ++ content(l2))

    @induct
    def concat0(l1: List, l2: List, l3: List) : List = (l1 match {
      case Nil() => l2 match {
        case Nil() => reverse(l3)
        case Cons(y, ys) => {
          concat0(Nil(), ys, Cons(y, l3))
        }
      }
      case Cons(x, xs) => concat0(xs, l2, Cons(x, l3))
    }) ensuring(content(_) == content(l1) ++ content(l2) ++ content(l3))

    // proved with unrolling=2 ???
    def property1(l1: List, l2: List) : Boolean = {
      reverse(concat(l1, l2)) == concat(reverse(l2), reverse(l1))
    } // ensuring(_ == true)
}
