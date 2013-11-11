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
  } ensuring (res => size(res) == n && time <= 3*n + 2)

  def append(l1: List, l2: List): List = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => Cons(x, append(xs, l2))

  }) ensuring (res =>  size(l1) + size(l2) == size(res) && time <= 3*size(l1) + 2)
  
  def mult(x : Int, y : Int) : Int = {
      if(x == 0 || y == 0) 0
      else
    	  mult(x,y-1) + x
  } 

//  def f_worst(m: Int, n: Int): List = {
//    require(0 <= m && 0 <= n)
//    
//    if (m == 0) Nil()
//    else append(f_worst(m - 1, n), genL(n))
//    
//  } ensuring(res => size(res) == mult(n, m) template((a,b,c) => time <= a*mult(mult(n,m),m+1) + c))

  def f_worst(m: Int, n: Int): List = {
    require(0 <= m && 0 <= n)
    if (m == 0) Nil()
    else append(genL(n), f_worst(m - 1, n))
    
  } ensuring(res => size(res) == mult(n, m) && time <= 5*size(res) + 6)
}
