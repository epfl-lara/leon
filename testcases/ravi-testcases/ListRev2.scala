object ListRev2 {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    // proved with unrolling=0
    def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) ensuring(res => res >= 0)

    def append(l1 : List, l2 : List) : List = (l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, append(xs, l2))
    }) ensuring(res => size(res) == size(l1) + size(l2))
    
    def reverse(l: List) : List = {
      l match{
        case Nil() => l
        case Cons(hd,tl) => append(reverse(tl),Cons(hd,Nil()))
      }
    } ensuring(res => size(res) == size(l))
}
