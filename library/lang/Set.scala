package leon.lang
import leon.annotation._

object Set {
  @library
  def empty[T] = Set[T]()
}

@ignore
case class Set[T](elems: T*) {
  def +(a: T): Set[T] = ???
  def ++(a: Set[T]): Set[T] = ???
  def -(a: T): Set[T] = ???
  def --(a: Set[T]): Set[T] = ???
  def contains(a: T): Boolean = ???
  def isEmpty: Boolean = ???
  def subsetOf(b: Set[T]): Boolean = ???
  def &(a: Set[T]): Set[T] = ???
}
