import funcheck.Utils._
import funcheck.Annotations._
import scala.annotation.tailrec

object Debug {
  sealed abstract class List
  case class Nil() extends List
  case class Cons(head: Int, tail: List) extends List

  def size1(list: List) : Int = {
    list match {
      case Nil() => 0
      case Cons(_, xs) => 1 + size1(xs)
    }
  } ensuring(_ >= 0)

  def size2(list: List) : Int = {
    sizeTailRec(list, 0)
  }

  def identity(list: List) : List = list
  
  def zero() : Int = 0

  def sizeTailRec(list: List, acc: Int) : Int = {
    require(acc >= 0)
    list match {
      case Nil() => acc
      case Cons(_, xs) => sizeTailRec(xs, acc + 1)
    }
  } ensuring(_ == acc + size1(list))

  def sizesAreTheSame(list: List) : Boolean = {
    size1(list) == size2(list)
  } holds

  def bug(list: List) : Boolean = {
    list match {
      case Nil() => true
      case Cons(_,_) => size1(list) == size2(list) + 1
    }
  } holds
}
