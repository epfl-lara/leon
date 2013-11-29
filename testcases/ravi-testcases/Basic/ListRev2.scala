import leon.Utils._

object ListRev2 {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) ensuring(_ >= 0)    
    //ensuring(res => true template((e,f) => e*res + f <= 0))    
    
    /*def mult(x : Int, y : Int) : Int = {
      if(x == 0 || y == 0) 0
      else
    	  mult(x-1,y-1) +  x + y - 1
    } ensuring(res => true template((e,f) => e*res + f <= 0))*/
    //ensuring(res => true template((e,f) => e*res + f <= 0))
        
    def reverse(l: List) : List = {
      l match{
        case Nil() => l
        case Cons(hd,tl) => append(reverse(tl),Cons(hd,Nil()))
      }
    } ensuring(res => size(res) == size(l))    
    //ensuring(res => (size(res) == size(l)) template((a,b) => time <= a*mult(size(l),size(l)) + b))
    //ensuring(res => (size(res) == size(l)) && time <= 5*mult(size(l),size(l)) + 3)
    //ensuring(res => (size(res) == size(l)) template((a,b) => time <= a*mult(size(l),size(l)) + b))    
    
    def append(l1 : List, l2 : List) : List = (l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, append(xs, l2))
    }) ensuring(res => size(l1) + size(l2)  == size(res)) 
    //template((c,d) => time <= c*size(l1) + d))
    //ensuring(res => size(l1) + size(l2)  == size(res) template((c,d) => time <= c*size(l1) + d))
    //ensuring(res => size(l1) + size(l2)  == size(res) && time <= 4*size(l1) + 2) 
    //ensuring(res => true template((p,q) => time <= p*size(l1) + q))
    //ensuring(res => true template((p,q,r) => p*size(l1) + q*size(l2) + r*size(res) == 0))    
}
