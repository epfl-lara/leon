import scala.collection.immutable.Set
import funcheck.Utils._

object AssociativeList { 
  sealed abstract class KeyValuePairAbs
  case class KeyValuePair(key: Int, value: Int) extends KeyValuePairAbs

  sealed abstract class List
  case class Cons(head: KeyValuePairAbs, tail: List) extends List
  case class Nil() extends List

  sealed abstract class OptInt
  case class Some(i: Int) extends OptInt
  case class None() extends OptInt

  def domain(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(KeyValuePair(k,_), xs) => Set(k) ++ domain(xs)
  }

  def content(l: List): Set[KeyValuePairAbs] = l match {
    case Nil() => Set.empty[KeyValuePairAbs]
    case Cons(KeyValuePair(k, v), xs) => Set(KeyValuePair(k, v)) ++ content(xs)
  }

  def noDuplicates(l: List): Boolean = l match {
    case Nil() => true
    case Cons(KeyValuePair(k, v), xs) => find(xs, k) == None() && noDuplicates(xs)
  }

  def update(l1: List, l2: List): List = (l2 match {
    case Nil() => l1
    case Cons(x, xs) => update(updateElem(l1, x), xs)
  }) ensuring(domain(_) == domain(l1) ++ domain(l2))

  def updateElem(l: List, e: KeyValuePairAbs): List = (l match {
    case Nil() => Cons(e, Nil())
    case Cons(KeyValuePair(k, v), xs) => e match {
      case KeyValuePair(ek, ev) => if (ek == k) updateElem(xs, e) else Cons(KeyValuePair(k, v), updateElem(xs, e))
    }
  }) ensuring(res => e match {
    case KeyValuePair(k, v) => domain(res) == domain(l) ++ Set[Int](k)
  })

  def induct0(l: List, p: KeyValuePairAbs, e: Int): Boolean = (l match {
    case Nil() => true
    case Cons(x, xs) => induct0(xs, p, e)
  }) ensuring(res => res && (p match {
    case KeyValuePair(k, v) => if (e == k) find(updateElem(l, p), e) == Some(v) else find(updateElem(l, p), e) == find(l, e)
  }))

  /*def induct1(l1: List, l2: List, e: Int): Boolean = {
    require(noDuplicates(l1) && noDuplicates(l2))
    l2 match {
      case Nil() => true
      case Cons(x, xs) => induct1(l1, xs, e)
    }
  } ensuring(res => res && (find(l2, e) match {
    case Some(v) => find(update(l1, l2), e) == Some(v)
    case None() => find(update(l1, l2), e) == find(l1, e)
  }))*/

  def inductNil(l: List, e: Int): Boolean = {
    require(noDuplicates(l))
    l match {
      case Nil() => true
      case Cons(x, xs) => inductNil(xs, e)
    }
  } ensuring(res => res && (find(update(Nil(), l), e) == find(l, e)))

  def prop0(e: Int): Boolean = (find(update(Nil(), Nil()), e) == find(Nil(), e)) holds

  def find(l: List, e: Int): OptInt = l match {
    case Nil() => None()
    case Cons(KeyValuePair(k, v), xs) => if (k == e) Some(v) else find(xs, e)
  }

  def main(args: Array[String]): Unit = {
    val l = Cons(KeyValuePair(6, 1), Cons(KeyValuePair(5, 4), Cons(KeyValuePair(3, 2), Nil())))
    val e = 0
    println(find(update(Nil(), l), e))
    println(find(l, e))
  }
}
