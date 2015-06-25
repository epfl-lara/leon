import leon.lang.Set
import leon.lang.synthesis._
object Sort {
  sealed abstract class List
  case object Nil extends List
  case class Cons(head: BigInt, tail: List) extends List

  def content(l: List): Set[BigInt] = l match {
    case Nil => Set()
    case Cons(i, t) => Set(i) ++ content(t)
  }
  def c1 = content(Cons(15, Cons(5, Cons(15, Nil))))

  def isSorted(l: List): Boolean = l match {
    case Nil => true
    case Cons(_,Nil) => true
    case Cons(x1, Cons(x2, rest)) => 
      x1 < x2 && isSorted(Cons(x2,rest))
  }
  def t1 = isSorted(Cons(10, Cons(20, Nil)))
  def t2 = isSorted(Cons(15, Cons(15, Nil)))

/*
  def sortMagic(l: List) = {
     ???[List]
  } ensuring((res:List) => 
    isSorted(res) && content(res) == content(l))
*/

  // def mm = sortMagic(Cons(20, Cons(5, Cons(50, Cons(2, Nil)))))
  // try replacing 50 with 5





/*
  def sInsert(x: BigInt, l: List): List = {
    require(isSorted(l))
    l match {
      case Nil => Cons(x, Nil)
      case Cons(e, rest) if (x == e) => l
      case Cons(e, rest) if (x < e) => Cons(x, Cons(e,rest))
      case Cons(e, rest) if (x > e) => Cons(e, sInsert(x,rest))
    }
  } ensuring {(res:List) => 
     isSorted(res) && content(res) == content(l) ++ Set(x)}
*/

  // We can also synthesize the body of sInsert interactively

/*
  def sInsert(x: BigInt, l: List): List = {
    require(isSorted(l))
    ???[List]
  } ensuring {(res:List) => 
     isSorted(res) && content(res) == content(l) ++ Set(x)}
 */

  // Fully automatic synthesis of sInsert also works

/* 
  // Or, we can repair an incorrect (overly simplified) program
  def sInsert(x: BigInt, l: List): List = {
    require(isSorted(l))
    l match {
      case Nil => Cons(x, Nil)
      case Cons(e, rest) => Cons(e, sInsert(x,rest))
    }
  } ensuring {(res:List) => 
     isSorted(res) && content(res) == content(l) ++ Set(x)}
 */

}
