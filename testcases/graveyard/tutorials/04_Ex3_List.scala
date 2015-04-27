import leon.Annotations._
import leon.Utils._

/*
  1) Add pre- and postconditions, or fix the code such that the following 
  functions verify:
  zip, sizesAreEquiv, reverse, concat0
  The postconditions on these functions give what should be checked, i.e.
  they should not be changed.

  2) find out what the function drunk does, and check provide a correct
    postcondition that relates the sizes of the input list with the output list

  3) the function appendAssoc is meant to prove that the appending lists is
    associative. Formulate this predicate and make sure Leon can verify it.
*/

object ListWithSize {
    sealed abstract class List
    case class Cons(head: BigInt, tail: List) extends List
    case class Nil() extends List

    sealed abstract class IntPairList
    case class IPCons(head: IntPair, tail: IntPairList) extends IntPairList
    case class IPNil() extends IntPairList

    sealed abstract class IntPair
    case class IP(fst: BigInt, snd: BigInt) extends IntPair

    
    def size(l: List) : BigInt = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    })

    def iplSize(l: IntPairList) : BigInt = (l match {
      case IPNil() => 0
      case IPCons(_, xs) => 1 + iplSize(xs)
    })

    // Verify
    def zip(l1: List, l2: List) : IntPairList = {
      l1 match {
        case Nil() => IPNil()
        case Cons(x, xs) => l2 match {
          case Cons(y, ys) => IPCons(IP(x, y), zip(xs, ys))
        }
      }
    } ensuring(iplSize(_) == size(l1))

    def sizeTailRec(l: List) : BigInt = sizeTailRecAcc(l, 0)
    def sizeTailRecAcc(l: List, acc: BigInt) : BigInt = {
     l match {
       case Nil() => acc
       case Cons(_, xs) => sizeTailRecAcc(xs, acc+1)
     }
    } 

    // Verify
    def sizesAreEquiv(l: List) : Boolean = {
      size(l) == sizeTailRec(l)
    } holds

    def content(l: List) : Set[BigInt] = l match {
      case Nil() => Set.empty[BigInt]
      case Cons(x, xs) => Set(x) ++ content(xs)
    }

    def sizeAndContent(l: List) : Boolean = {
      size(l) == 0 || content(l) != Set.empty[BigInt]
    } holds
    
    def drunk(l : List) : List = (l match {
      case Nil() => Nil()
      case Cons(x,l1) => Cons(x,Cons(x,drunk(l1)))
    }) // TODO: find postcondition

    
    def funnyCons(x: BigInt, l: List) : List = (l match {
        case Nil() => Cons(x, Nil())
        case c @ Cons(_,_) => Cons(x, c)
    }) ensuring(size(_) > 0)

    // Verify
    def reverse(l: List) : List = reverse0(l, Nil()) ensuring(content(_) == content(l))
    def reverse0(l1: List, l2: List) : List = (l1 match {
      case Nil() => l2
      case Cons(x, xs) => reverse0(xs, Cons(x, l2))
    }) 

    def append(l1 : List, l2 : List) : List = (l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, append(xs, l2))
    }) ensuring(content(_) == content(l1) ++ content(l2))

    @induct
    def nilAppend(l : List) : Boolean = (append(l, Nil()) == l) holds

    // TODO: find predicate
    //@induct
    //def appendAssoc(xs : List, ys : List, zs : List) : Boolean =
    //  (...) holds

    @induct
    def sizeAppend(l1 : List, l2 : List) : Boolean =
      (size(append(l1, l2)) == size(l1) + size(l2)) holds

    @induct
    def concat(l1: List, l2: List) : List = 
      concat0(l1, l2, Nil()) ensuring(content(_) == content(l1) ++ content(l2))

    @induct
    def concat0(l1: List, l2: List, l3: List) : List = (l1 match {
      case Nil() => l2 match {
        case Nil() => reverse(l2)
        case Cons(y, ys) => {
          concat0(Nil(), ys, Cons(y, l3))
        }
      }
      case Cons(x, xs) => concat0(xs, l2, Cons(x, l3))
    }) ensuring(content(_) == content(l1) ++ content(l2) ++ content(l3))

}
