import scala.collection.immutable.Set
import funcheck.Annotations._

object ListWithSize {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    // proved with unrolling=0
    def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) ensuring(_ >= 0)

    def content(l: List) : Set[Int] = l match {
      case Nil() => Set.empty[Int]
      case Cons(x, xs) => Set(x) ++ content(xs)
    }

    // proved with unrolling=1
    def funnyCons(x: Int, l: List) : List = (l match {
        case Nil() => Cons(x, Nil())
        case c @ Cons(_,_) => Cons(x, c)
    }) ensuring(size(_) > 0)

    // proved with unrolling=2
    def reverse(l: List) : List = reverse0(l, Nil()) // ensuring(content(_) == content(l))
    def reverse0(l1: List, l2: List) : List = l1 match {
      case Nil() => l2
      case Cons(x, xs) => reverse0(xs, Cons(x, l2))
    }

    def append(l1 : List, l2 : List) : List = (l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, append(xs, l2))
    })

    @induct
    def propAppend1(l : List) : Boolean = {
      append(l, Nil()) == l
    } ensuring(_ == true)

    def propAppend2(l : List) : Boolean = (l match {
      case Nil() => propAppend1(l)
      case Cons(x,xs) => (!propAppend1(xs) || propAppend1(l))
    }) ensuring (_ == true)

    def propAppend3(l : List) : Boolean = {
      !propAppend1(l) || propAppend2(l)
    } ensuring (_ == true)

/*
    def induct(l : List, prop : List => Boolean) = {
      case Nil() => prop(l)
      case Cons(x,xs) => (!prop(xs) || prop(l))
    }
*/

    // proved with unrolling=4
    def concat(l1: List, l2: List) : List = concat0(l1, l2, Nil()) 
     // ensuring(content(_) == content(l1) ++ content(l2))
    def concat0(l1: List, l2: List, l3: List) : List = (l1 match {
      case Nil() => l2 match {
        case Nil() => reverse(l3)
        case Cons(y, ys) => {
          concat0(Nil(), ys, Cons(y, l3))
        }
      }
      case Cons(x, xs) => concat0(xs, l2, Cons(x, l3))
    }) //ensuring(content(_) == content(l1) ++ content(l2) ++ content(l3))

    // proved with unrolling=2 ???
    def property1(l1: List, l2: List) : Boolean = {
      reverse(concat(l1, l2)) == concat(reverse(l2), reverse(l1))
    } ensuring(_ == true)
}
