import funcheck.Utils._
import funcheck.Annotations._

object AssociativeList { 
  sealed abstract class KeyValuePairAbs
  case class KeyValuePair(key: Int, value: Int) extends KeyValuePairAbs

  sealed abstract class List
  case class Cons(head: KeyValuePairAbs, tail: List) extends List
  case class Nil() extends List

  def size(l : List) : Int = (l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def asMap(l : List) : Map[Int,Int] = (l match {
    case Nil() => Map.empty[Int,Int]
    case Cons(KeyValuePair(k,v), t) => asMap(t).updated(k, v)
  })

  sealed abstract class OptionInt
  case class Some(i: Int) extends OptionInt
  case class None() extends OptionInt

  def domain(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(KeyValuePair(k,_), xs) => Set(k) ++ domain(xs)
  }

  def find(l: List, k0: Int): OptionInt = (l match {
    case Nil() => None()
    case Cons(KeyValuePair(k, v), xs) => if (k == k0) Some(v) else find(xs, k0)
  }) ensuring(res => res match {
    case None() => !asMap(l).isDefinedAt(k0)
    case Some(v) => asMap(l).isDefinedAt(k0) && asMap(l)(k0) == v
  })

  def noDuplicates(l: List): Boolean = l match {
    case Nil() => true
    case Cons(KeyValuePair(k, v), xs) => find(xs, k) == None() && noDuplicates(xs)
  }

//  @induct
  def updateElem(l: List, k0: Int, v0: Int): List = (l match {
    case Nil() => Cons(KeyValuePair(k0, v0), Nil())
    case Cons(KeyValuePair(k, v), xs) => if(k0 == k) Cons(KeyValuePair(k0, v0), xs) else Cons(KeyValuePair(k, v), updateElem(xs, k0, v0))
  }) ensuring(res => {
    asMap(res).isDefinedAt(k0) && asMap(res)(k0) == v0
  })

  @induct
  def readOverWrite(l: List, k1: Int, k2: Int, e: Int) : Boolean = {
    find(updateElem(l, k2, e), k1) == (if (k1 == k2) Some(e) else find(l, k1))
  } holds

  def prop1(l : List) : Boolean = {
    (l == Nil()) == (asMap(l) == Map.empty[Int,Int])
  } holds

  def weird(m : Map[Int,Int], k : Int, v : Int) : Boolean = {
    !(m(k) == v) || m.isDefinedAt(k)
  } holds

  // def prop0(l : List, m : Map[Int,Int]) : Boolean = {
  //   size(l) > 4 && asMap(l) == m
  // } ensuring(res => !res)
}
