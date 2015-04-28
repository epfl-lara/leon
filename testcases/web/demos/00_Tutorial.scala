import leon.lang._
import leon.lang.synthesis._
import leon.annotation._
object Sort {
// ==================================================================
//                        Max
// ==================================================================

/*
  def max(x: Int, y: Int): Int = {
    val d = x - y
    if (d > 0) x
    else y
  } ensuring(res =>
    x <= res && y <= res && (res == x || res == y))

  def test1 = max(10, 5)
  def test2 = max(-5, 5)
  def test3 = max(-5, -7)

  def test4 = max(-1639624704, 1879048192)
 */

/*
def max(x: BigInt, y: BigInt): BigInt = {
  val d = x - y
  if (d > 0) x
  else y
} ensuring(res =>
  x <= res && y <= res && (res == x || res == y))
 */

/*
def max(x: BigInt, y: BigInt): BigInt = {
  val d = x - y
  if (d > 0) x
  else y
} ensuring(res =>  res==rmax(x,y))

def rmax(x: BigInt, y: BigInt) =
  if (x <= y) x else y
 */

/*
def max_lemma(x: BigInt, y: BigInt, z: BigInt): Boolean = {
  max(x,x) == x &&
  max(x,y) == max(y,x) &&
  max(x,max(y,z)) == max(max(x,y), z) &&
  max(x,y) + z == max(x + z, y + z)
} holds
 */

/*
def max(x: Int, y: Int): Int = {
  require(0 <= x && 0 <= y)
  val d = x - y
  if (d > 0) x
  else y
} ensuring (res =>
  x <= res && y <= res && (res == x || res == y))
 */

// ==================================================================
//                        Sort 2-3 ELements
// ==================================================================

/*
  def sort2(x : BigInt, y : BigInt) = choose{(res: (BigInt,BigInt)) =>
    Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
  }
*/

/*
  def sort2(x : BigInt, y : BigInt) = {
    ???[(BigInt, BigInt)]
  } ensuring{(res: (BigInt,BigInt)) =>
    Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
  }
*/


// def testSort2 = sort2(30, 4)

/*
  def sort2(x: BigInt, y: BigInt) = choose{(res: (BigInt,BigInt)) => 
    sort2spec(x,y,res)
  }

  def sort2spec(x: BigInt, y: BigInt, res: (BigInt, BigInt)): Boolean = {
    Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
  }

  def unique2(x: BigInt, y: BigInt,
              res1: (BigInt, BigInt),
              res2: (BigInt, BigInt)): Boolean = {
    require(sort2spec(x,y,res1) && sort2spec(x,y,res2))
    res1 == res2
  } holds
 */

/*
  def sort3spec(x: BigInt, y: BigInt, z: BigInt, res: (BigInt,BigInt,BigInt)): Boolean = {
    Set(x,y,z) == Set(res._1, res._2, res._3) && 
    res._1 <= res._2 && res._2 <= res._3
  }

  def unique3(x: BigInt, y: BigInt, z: BigInt,
         res1: (BigInt,BigInt,BigInt),
         res2: (BigInt,BigInt,BigInt)): Boolean = {
    require(sort3spec(x,y,z,res1) && sort3spec(x,y,z,res2))
    res1 == res2
  }.holds
 */

// ==================================================================
//                        Sort a List
// ==================================================================

/*
  sealed abstract class List
  case object Nil extends List
  case class Cons(head: BigInt, tail: List) extends List

  def size(l: List): BigInt = (l match {
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
  def isSorted(l: List): Boolean = l match {
    case Nil => true
    case Cons(_,Nil) => true
    case Cons(x1, Cons(x2, rest)) => 
      x1 < x2 && isSorted(Cons(x2,rest))
  }
*/
  //def t1 = isSorted(Cons(10, Cons(20, Nil)))
  //def t2 = isSorted(Cons(15, Cons(15, Nil)))

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
  def sortMagic(l: List) = {
     ???[List]
  } ensuring((res:List) => 
    isSorted(res) && content(res) == content(l))
*/

  // def mm = sortMagic(Cons(20, Cons(5, Cons(50, Cons(2, Nil)))))

/*
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
