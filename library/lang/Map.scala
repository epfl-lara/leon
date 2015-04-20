package leon.lang
import leon.annotation._

object Map {
  @library
  def empty[A,B] = Map[A,B]()
}

@ignore
case class Map[A, B](elems: (A, B)*) {
  def apply(k: A): B = ???
  def ++(b: Map[A, B]): Map[A,B] = ???
  def updated(k: A, v: B): Map[A,B] = ???
  def contains(a: A): Boolean = ???
  def isDefinedAt(a: A): Boolean = contains(a)
}
