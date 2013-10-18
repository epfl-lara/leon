import leon.Utils._

object ListWithSize {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List
     
    def size(l: List) : Int = (l match { 
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) 
    //ensuring(res => true template((a) => a*res <= 0 ))

    def append(l1 : List, l2 : List) : List = (l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, append(xs, l2))

    }) ensuring(res => true template((a,b,c) => time <= a*size(l1) + b*size(l2) + c)) 
    //ensuring(res => size(res) != size(l1) - 1)
    //template((a,b,c) => a*size(l1) + b*size(res) <= 0)
}
