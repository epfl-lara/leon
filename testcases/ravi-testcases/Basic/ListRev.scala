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
    }) ensuring(res => size(res) == size(l1) + size(l2))
}
