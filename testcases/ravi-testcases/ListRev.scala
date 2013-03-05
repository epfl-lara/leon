object ListWithSize {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    // proved with unrolling=0
    def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) ensuring(res => res >= 0)

    // proved with unrolling=2
    def reverse(l: List) : List = {
      reverse0(l, Nil())  
    } ensuring(res => size(res) == size(l))
    
    def reverse0(l1: List, l2: List) : List = (l1 match {
      case Nil() => l2
      case Cons(x, xs) => reverse0(xs, Cons(x, l2))
    }) //ensuring(res => size(res) == size(l1) + size(l2))

    /*def append(l1 : List, l2 : List) : List = (l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, append(xs, l2))
    }) ensuring(content(_) == content(l1) ++ content(l2))

    @induct
    def nilAppend(l : List) : Boolean = (append(l, Nil()) == l) holds

    // unclear if we needed this--it was meant to force folding
    //def appendFold(x : Int, xs : List, ys : List) : Boolean = {
    //  true
    //} ensuring (res => res && Cons(x,append(xs, ys)) == append(Cons(x,xs), ys))

    @induct
    def appendAssoc(xs : List, ys : List, zs : List) : Boolean =
      (append(append(xs, ys), zs) == append(xs, append(ys, zs))) holds

    def revAuxBroken(l1 : List, e : Int, l2 : List) : Boolean = {
      (append(reverse(l1), Cons(e,l2)) == reverse0(l1, l2))
    } // holds

    @induct
    def reverse0exposed(l1 : List, l2 : List) : Boolean = {
      (reverse0(l1, l2) == append(reverse(l1), l2))
    } // holds

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

    def reverseConcat0(l1: List, l2: List) : Boolean = {
      reverse(concat(l1, l2)) == concat(reverse(l2), reverse(l1))
    } // holds

    // proved with unrolling=2 ???
    def reverseConcat(l1: List, l2: List) : Boolean = {
      reverse(concat(l1, l2)) == concat(reverse(l2), reverse(l1))
    } // holds
*/}
