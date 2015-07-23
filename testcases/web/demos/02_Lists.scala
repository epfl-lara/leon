import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object List {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case object Nil extends List

  def size(l: List) : BigInt = (l match {
      case Nil => BigInt(0)
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[BigInt] = l match {
    case Nil => Set()
    case Cons(i, t) => Set(i) ++ content(t)
  }



  def insertUnique(l: List, v: BigInt): List = (l match {
    case Cons(h, t) =>
      if (h == v) {
        l
      } else {
        Cons(h, insertUnique(t, v))
      }
    case Nil =>
      Cons(v, Nil)
  }) ensuring { (res: List) =>
    true
    //content(res) == content(l) ++ Set(v) &&
    //size(res) >= size(l)
  }




  def delete(l: List, v: BigInt): List = {
    choose{ (res: List) =>
      content(res) == content(l) -- Set(v)
    }
  }

}
