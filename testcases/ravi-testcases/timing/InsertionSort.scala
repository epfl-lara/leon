import leon.lang.invariantLang._

object InsertionSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  def size(l : List) : Int = (l match {    
    case Cons(_, xs) => 1 + size(xs)
    case _ => 0
  })    

  def sortedIns(e: Int, l: List): List = {   
    l match {      
      case Cons(x,xs) => if (x <= e) Cons(x,sortedIns(e, xs)) else Cons(e, l)
      case _ => Cons(e,Nil())
    } 
  } ensuring(res => size(res) == size(l) + 1 template((a,b) => time <= a*size(l) +b))

  def sort(l: List): List = (l match {    
    case Cons(x,xs) => sortedIns(x, sort(xs))
    case _ => Nil()
    
  }) ensuring(res => size(res) == size(l) template((a,b) => time <= a*(size(l)*size(l)) +b))  
}
