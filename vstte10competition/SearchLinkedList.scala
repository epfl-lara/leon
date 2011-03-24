import scala.collection.immutable.Set
import funcheck.Utils._
import funcheck.Annotations._

object SearchLinkedList {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  @induct
  def firstZero(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(x, xs) => if (x == 0) 0 else firstZero(xs) + 1
  }) ensuring (res => if (!contains(list, 0)) res == size(list) else zeroAt(list, res))

  def zeroAt(list : List, pos : Int) : Boolean = {
    require(pos >= 0)
    list match {
      case Nil() => false
      case Cons(x, xs) => if (pos == 0) x == 0 else zeroAt(xs, pos - 1)
    }
  }

  def prop0(list : List, pos : Int) : Boolean = {
    require(pos >= 0)
    list match {
      case Nil() => true
      case Cons(x, xs) => if (zeroAt(xs, pos)) zeroAt(list, pos + 1) else true
    } 
  } holds

  def firstZeroAtPos(list : List, pos : Int) : Boolean = {
    require(pos >= 0)
    list match {
      case Nil() => false
      case Cons(x, xs) => if (pos == 0) x == 0 else x != 0 && firstZeroAtPos(xs, pos - 1)
    }
  } ensuring (res => if (res) contains(list, 0) else true)

  def contains(list : List, elem : Int) : Boolean = (list match {
    case Nil() => false
    case Cons(x, xs) => x == elem || contains(xs, elem)
  })
}
