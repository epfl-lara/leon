import leon.lang._
import leon.annotation._

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

  def find(l: List, e: Int): OptInt = l match {
    case Nil() => None()
    case Cons(KeyValuePair(k, v), xs) => if (k == e) Some(v) else find(xs, e)
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
      case KeyValuePair(ek, ev) => if (ek == k) Cons(KeyValuePair(ek, ev), xs) else Cons(KeyValuePair(k, v), updateElem(xs, e))
    }
  }) ensuring(res => e match {
    case KeyValuePair(k, v) => domain(res) == domain(l) ++ Set[Int](k)
  })

  @induct
  def readOverWrite(l: List, e: KeyValuePairAbs, k: Int) : Boolean = (e match {
    case KeyValuePair(key, value) =>
      find(updateElem(l, e), k) == (if (k == key) Some(value) else find(l, k))
  }) holds

  // def prop0(e: Int): Boolean = (find(update(Nil(), Nil()), e) == find(Nil(), e)) holds

  def main(args: Array[String]): Unit = {
    val l = Cons(KeyValuePair(6, 1), Cons(KeyValuePair(5, 4), Cons(KeyValuePair(3, 2), Nil())))
    val e = 0
    println(find(update(Nil(), l), e))
    println(find(l, e))
  }
}
