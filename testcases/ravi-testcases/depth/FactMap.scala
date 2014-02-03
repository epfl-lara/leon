import leon.Utils._

object FactMap {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List): Int = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  })
    
  /*def doubleMap(l: List): List = (l match {
    case Nil() => Nil()
    case Cons(x, t) =>  {
      Cons(2*x, doubleMap(t))      
    }
  }) ensuring(res => true template((a,b) => depth <= a*size(l) + b))*/
  
  def fact(n : Int) : Int = {
    require(n >= 0)
    
    if(n == 1 || n == 0) 1
    else n * fact(n-1)
    
  } ensuring(res => true template((a,b) => depth <= a*n + b))
  
  def descending(l: List, k: Int) : Boolean = {
    l match {
      case Nil() => true
      case Cons(x, t) => x > 0 && x <= k && descending(t, x-1)
    }
  }
  
  def factMap(l: List, k: Int): List = {
    require(descending(l, k) && k >= 0)
    
   l match {    
    case Nil() => Nil()
    case Cons(x, t) =>  {
      val f = fact(x)
      Cons(f, factMap(t, x-1))      
    }
    
  }} ensuring(res => true template((a,b) => depth <= a*k + b)) 
}
