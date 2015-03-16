import leon.lang._
import leon.collection._

object Map {
  
  def failure1[T](l: List[T], f: T => T): Boolean = {
    l.map(f) == l.map(f).map(f)
  }.holds

  def failure2[T](l: List[T], f: T => T): Boolean = {
    l.map(f) == (l match {
      case Cons(head, tail) => Cons(head, tail.map(f))
      case Nil() => Nil[T]()
    })
  }.holds

  def failure3[T](l: List[T], f: T => List[T]): Boolean = {
    l == l.flatMap(f)
  }.holds
}
