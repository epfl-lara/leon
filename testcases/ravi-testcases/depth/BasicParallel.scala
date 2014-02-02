import leon.Utils._

object BasicParallel {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List): Int = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  })
  
  //a program with linear depth
  def doubleMap(l: List): List = (l match {
    case Nil() => Nil()
    case Cons(x, t) =>  {
      Cons(2*x, doubleMap(t))      
    }
  }) ensuring(res => true template((a,b) => depth <= a*size(l) + b))
  
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
  
  //a program that removes from a list, all multiples of a number 'i' upto 'n'
  //the depth of this program is again 1
//  def removeMultiples(l: List, i: Int, n: Int, incr: Int): (List, Int) = {
//    require(i >= 0 && incr >= 1 && i <= n)
//    l match {
//      case Nil() => (Nil(), 0)
//      case Cons(x, t) => {
//        if (x < i) {
//          val (r,d) = removeMultiples(t, i, n, incr)
//          (Cons(x, r), max(d, 2))
//
//        } else if (x > i) {
//          val ni = i + incr
//          if (ni > n) (l, 2)
//          else {
//            val (r,d) = removeMultiples(l, ni, n, incr)
//            (r, max(d, 2))
//          }      
//            
//
//        } else {
//          val ni = i + incr
//          if (ni > n) (t, 2)
//          else{
//            val (r,d) = removeMultiples(l, ni, n, incr)
//            (r, max(d, 2))
//          }            
//        }
//      }
//    }
//  } //ensuring (res => true template ((a) => res._2 <= a))
  //ensuring (res => true template ((a,b) => time <= a*(size(l) + n - i) + b))
  
  //another function with constant depth
//  def createList(i: Int, n: Int) : (List, Int) = {
//    require(i <= n)
//    if(n == i) (Nil(), 0)
//    else {
//      val (r, d) = createList(i+1, n)
//      (Cons(i, r), max(d, 2))
//    }          	
//  } //ensuring(res => true template((a) => res._2 <= a))
  //ensuring(res => true template((a,b) => time <= a*(n-i) + b))
  
//  def removeNonPrimes(currval: Int, l: List, n: Int, sqrtn: Int): (List, Int) = {
//    require(currval <= sqrtn && sqrtn <= n && currval >= 1)
//    
//    val (r,d) = removeMultiples(l, currval, n, currval)
//    if(currval == sqrtn) {
//      (r, d + 2)
//    } else {
//      val (res, t) = removeNonPrimes(currval + 1, r, n, sqrtn)
//      (res, t + 2)
//    }      
//  } //ensuring(res => true template((a,b) => res._2 <= a*(sqrtn - currval) + b))
  
//  def simplePrimes(n: Int, sqrtn : Int) : (List, Int) = {
//    require(sqrtn >= 2 && sqrtn <= n)
//    
//     val (l, d1) = createList(2, n)
//     val (resl, t2) = removeNonPrimes(2, l, n, sqrtn)
//     (resl, d1 + t2 + 3) 
//  }  //ensuring(res => true template((a,b) => res._2 <= a*sqrtn + b)) 
}
