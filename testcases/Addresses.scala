import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object Addresses {
  // list of integers
  sealed abstract class List
  case class Cons(a:Int,b:Int,c:Int, tail:List) extends List
  case class Nil() extends List

  def empty() = Set.empty[Int]

  def setA(l:List) : Set[Int] = l match {
    case Nil() => empty
    case Cons(a,b,c,l1) => Set(a) ++ setA(l1)
  }

  def containsA(x:Int,l:List) : Boolean = (l match {
    case Nil() => false
    case Cons(a,b,c,t) => a==x || containsA(x,t)
  }) ensuring (res => res == (setA(l) contains x))

  def theseAunique1(as:Set[Int],l:List) : Boolean = l match {
    case Nil() => true
    case Cons(a,b,c,l1) => 
      theseAunique1(as,l1) && !(as contains a) && (setA(l1) contains a)
  }

  def theseAunique2(as:Set[Int],l:List) : Boolean = (l match {
    case Nil() => true
    case Cons(a,b,c,l1) => 
      theseAunique2(as,l1) && !(as contains a) && containsA(a,l1)
  }) ensuring (res => res==theseAunique1(as,l))

  def disjoint(x:Set[Int],y:Set[Int]):Boolean =
    x.intersect(y).isEmpty

  def uniqueAbsentAs(unique:Set[Int],absent:Set[Int],l:List) : Boolean = (l match {
    case Nil() => true
    case Cons(a,b,c,l1) => {
      !(absent contains a) &&
      (if (unique contains a) uniqueAbsentAs(unique -- Set(a), absent ++ Set(a), l1)
       else uniqueAbsentAs(unique, absent, l1))
    }
  }) ensuring (res => theseAunique1(unique,l) && disjoint(setA(l),absent))

  def allPos(l:List) : Boolean = l match {
    case Nil() => true
    case Cons(a,b,c,l1) => 0 <= a && 0 <= b && 0 <= c && allPos(l1)
  }

  def max(x:Int,y:Int) = if (x <= y) x else y

  def collectA(x:Int,l:List) : (Int,Int,List) = (l match {
    case Nil() => (0,0,Nil())
    case Cons(a,b,c,l1) if (a==x) => {
      val (b2,c2,l2) = collectA(x,l1)
      (max(b,b2),max(c,c2),l2)
    }
    case Cons(a,b,c,l1) if (a!=x) => {
      val (b2,c2,l2) = collectA(x,l1)
      (b2,c2,Cons(a,b,c,l2))
    }
  }) ensuring (res => {
    val (b,c,l1) = res
    !setA(l1).contains(x)
  })

  def makeUniqueA(x:Int,l:List) : List = {
    require(allPos(l))
    val (b,c,l1) = collectA(x,l)
    Cons(x,b,c,l1)
  } ensuring(res => theseAunique1(Set(x),res))
}
