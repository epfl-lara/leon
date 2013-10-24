import leon.Utils._

object ListRev2 {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) 
        
    def reverse(l: List) : List = {
      l match{
        case Nil() => l
        case Cons(hd,tl) => append(reverse(tl),Cons(hd,Nil()))
      }
    } ensuring(res => true template((a,b) => time <= a*size(l) + b)) 
    //ensuring(res => size(res) == size(l))

    def append(l1 : List, l2 : List) : List = (l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, append(xs, l2))
    }) ensuring(res => true template((p,q) => time <= p*size(l1) + q))
    //ensuring(res => true template((p,q,r) => p*size(l1) + q*size(l2) + r*size(res) == 0))
    //ensuring(res => size(l1) + size(l2)  == size(res))    
}
