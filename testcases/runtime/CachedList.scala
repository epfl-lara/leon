import leon.lang._
import leon.lang.synthesis._

object SortedList {
  abstract class List
  case class Cons(h: Int, t: List) extends List
  case object Nil extends List

  def size(l: List): Int = l match {
    case Cons(h, t) => 1 + size(t)
    case Nil => 0
  }

  def content(l: List): Set[Int] = l match {
    case Cons(h, t) => Set(h) ++ content(t)
    case Nil => Set()
  }

  case class CachedList(cache: Int, data: List)

  def inv(cl: CachedList) = {
    (content(cl.data) contains cl.cache) || (cl.data == Nil)
  }

  def withCache(l: List): CachedList = choose {
    (x: CachedList) => inv(x) && content(x.data) == content(l)
  }

  def insert(l: CachedList, i: Int): CachedList = {
    require(inv(l))
    choose{ (x: CachedList) => content(x.data) == content(l.data) ++ Set(i) && inv(x) }
  }

  def delete(l: CachedList, i: Int): CachedList = {
    require(inv(l))
    choose{ (x: CachedList) => content(x.data) == content(l.data) -- Set(i) && inv(x) }
  }

  def contains(l: CachedList, i: Int): Boolean = {
    require(inv(l))
    choose{ (x: Boolean) => x == (content(l.data) contains i) }
  }
}
