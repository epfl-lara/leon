import scala.collection.immutable.Set
import leon.Utils._
import leon.Annotations._

object AssociativeListImp { 
  sealed abstract class KeyValuePairAbs
  case class KeyValuePair(key: Int, value: Int) extends KeyValuePairAbs

  sealed abstract class List
  case class Cons(head: KeyValuePairAbs, tail: List) extends List
  case class Nil() extends List

  sealed abstract class OptionInt
  case class Some(i: Int) extends OptionInt
  case class None() extends OptionInt

  def domain(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(KeyValuePair(k,_), xs) => Set(k) ++ domain(xs)
  }

  def findSpec(l: List, e: Int): OptionInt = l match {
    case Nil() => None()
    case Cons(KeyValuePair(k, v), xs) => if (k == e) Some(v) else find(xs, e)
  }

  def findLast(l: List, e: Int): OptionInt = {
    var res: OptionInt = None()
    var l2 = l
    while(!l2.isInstanceOf[Nil]) {
      val Cons(KeyValuePair(k, v), tail) = l2
      l2 = tail
      if(k == e)
        res = Some(v)
    }
    res
  } ensuring(res => findSpec(l, e) == res)

  def find(l: List, e: Int): OptionInt = {
    var res: OptionInt = None()
    var l2 = l
    var seen: List = Nil()
    (while(!l2.isInstanceOf[Nil]) {
      val Cons(head@KeyValuePair(k, v), tail) = l2
      seen = Cons(head, seen)
      l2 = tail
      if(res == None() && k == e)
        res = Some(v)
    }) invariant((res match {
         case Some(_) => domain(seen).contains(e)
         case None() => !domain(seen).contains(e)
       }) && domain(seen) ++ domain(l2) == domain(l))

    res
  } ensuring(res => res match {
     case Some(_) => domain(l).contains(e)
     case None() => !domain(l).contains(e)
  })

  def noDuplicates(l: List): Boolean = l match {
    case Nil() => true
    case Cons(KeyValuePair(k, v), xs) => find(xs, k) == None() && noDuplicates(xs)
  }

  def updateElem(l: List, e: KeyValuePairAbs): List = {
    var res: List = Nil()
    var l2 = l
    var found = false
    val KeyValuePair(ek, ev) = e
    (while(!l2.isInstanceOf[Nil]) {
      val Cons(KeyValuePair(k, v), tail) = l2
      l2 = tail
      if(k == ek) {
        res = Cons(KeyValuePair(ek, ev), res)
        found = true
      } else {
        res = Cons(KeyValuePair(k, v), res)
      }
    }) invariant(
        (if(found) 
           domain(res) ++ domain(l2) == domain(l) ++ Set(ek)
         else
           domain(res) ++ domain(l2) == domain(l)
        ))
    if(!found)
      Cons(KeyValuePair(ek, ev), res)
    else
      res
  } ensuring(res => e match {
    case KeyValuePair(k, v) => domain(res) == domain(l) ++ Set[Int](k)
  })

  @induct
  def readOverWrite(l: List, k1: Int, k2: Int, e: Int) : Boolean = {
    find(updateElem(l, KeyValuePair(k2,e)), k1) == (if (k1 == k2) Some(e) else find(l, k1))
  } //holds
}

