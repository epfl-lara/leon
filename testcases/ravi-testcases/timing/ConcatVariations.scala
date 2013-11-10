import leon.Utils._

object ListOperations {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List): Int = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  })

  def genL(n: Int): List = {
    require(n >= 0)
    if (n == 0) Nil()
    else
      Cons(n, genL(n - 1))
  } ensuring (res => size(res) == n) 

  def append(l1: List, l2: List): List = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => Cons(x, append(xs, l2))

  }) ensuring (res =>  size(l1) + size(l2) == size(res) template((a,b) => time <= a*size(l1) + b))

  def reverseRec(l1: List, l2: List): List = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => reverseRec(xs, Cons(x, l2))

  }) ensuring (res =>  size(l1) + size(l2) == size(res) template((a,b) => time <= a*size(l1) + b))

  def reverse(l: List): List = {
    reverseRec(l, Nil())
    
  } ensuring (res => size(l) == size(res) template((a,b) => time <= a*size(l) + b))
  
  def mult(x : Int, y : Int) : Int = {
      if(x == 0 || y == 0) 0
      else
    	  mult(x-1,y-1) +  x + y - 1
  } 

  def reverse2(l: List): List = {
    l match {
      case Nil() => l
      case Cons(hd, tl) => append(reverse2(tl), Cons(hd, Nil()))
    }
  } ensuring (res => size(res) == size(l) template((a,b) => time <= a*mult(size(l),size(l)) + b))

  def remove(elem: Int, l: List): List = {
    l match {
      case Nil() => Nil()
      case Cons(hd, tl) => if (hd == elem) remove(elem, tl) else Cons(hd, remove(elem, tl))
    }
  } ensuring (res => size(l) >= size(res) template((a,b) => time <= a*size(l) + b))

  def contains(list: List, elem: Int): Boolean = (list match {
    case Nil() => false
    case Cons(x, xs) => x == elem || contains(xs, elem)
    
  }) ensuring (res => true template((a,b) => time <= a*size(list) + b))

  def distinct(l: List): List = (
    l match {
      case Nil() => Nil()
      case Cons(x, xs) => {
        val newl = distinct(xs)
        if (contains(newl, x)) newl
        else Cons(x, newl)
      }
   }) ensuring (res => size(l) >= size(res) template((a,b) => time <= a*mult(size(l),size(l)) + b))
}
