import leon.lang._
import leon.lang.synthesis._
import leon.annotation._
object Sort {
/*
  def sort2(x : BigInt, y : BigInt) = choose{(res: (BigInt,BigInt)) =>
    Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
  }
*/

/*
  sealed abstract class List
  case object Nil extends List
  case class Cons(head: BigInt, tail: List) extends List

  def size(l: List) : BigInt = (l match {
      case Nil => 0
      case Cons(x, rest) => x + size(rest)
  }) 
*/
  // ensuring(res =>  res > 0)

  // def s1 = size(Cons(10, Cons(1000, Nil)))

/*
  def content(l: List): Set[BigInt] = l match {
    case Nil => Set()
    case Cons(i, t) => Set(i) ++ content(t)
  }
*/

/*
  def isSorted(l : List) : Boolean = l match {
    case Nil => true
    case Cons(_,Nil) => true
    case Cons(x1, Cons(x2, rest)) => 
      x1 < x2 && isSorted(Cons(x2,rest))
  }
*/
  //def t1 = isSorted(Cons(10, Cons(20, Nil)))
  //def t2 = isSorted(Cons(15, Cons(15, Nil)))

/*
  def sInsert(x : BigInt, l : List) : List = {
    require(isSorted(l))
    l match {
      case Nil => Cons(x, Nil)
      case Cons(e, rest) if (x == e) => l
      case Cons(e, rest) if (x < e) => Cons(x, Cons(e,rest))
      case Cons(e, rest) if (x > e) => Cons(e, sInsert(x,rest))
    }
  } ensuring {(res:List) => 
     isSorted(res) && content(res) == content(l) ++ Set(x)}

   // size(res) == size(l) + 1
*/

/*  
  def insertMagic(x: BigInt, l: List): List = {
    require(isSorted(l))
    choose {(res: List) => 
      isSorted(res) && content(res) == content(l) ++ Set[BigInt](x)
    }
  }
*/

  //def m = insertMagic(17, Cons(10, Cons(15, Cons(20, Nil))))

/*
  def sortMagic(l : List) = choose{(res:List) => 
    isSorted(res) && content(res) == content(l)
  }
*/

  // def mm = sortMagic(Cons(20, Cons(5, Cons(50, Cons(2, Nil)))))

}
