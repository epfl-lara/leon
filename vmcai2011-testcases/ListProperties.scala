import scala.collection.immutable.Set

object IntListProperties {
  sealed abstract class IntList
  case class Cons(head: Int, tail: IntList) extends IntList
  case class Nil() extends IntList

  def size(list: IntList) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def content(list: IntList) : Set[Int] = (list match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }) //ensuring(_.size <= size(list))

  def removeDuplicates(list: IntList) : IntList = (list match {
    case Nil() => Nil()
    case Cons(x, xs) => Cons(x, removeDuplicates(removeFrom(x, xs)))
  }) ensuring(newList => content(newList) == content(list))
  def removeFrom(v: Int, list: IntList) : IntList = (list match {
    case Nil() => Nil()
    case Cons(x, xs) => {
      val rest = removeFrom(v, xs)
      if(v == x) rest else Cons(x, rest)
    }
  }) ensuring(newList => content(newList) == content(list) -- Set(v))

//  def reverse(list: IntList) : IntList = reverse0(list, Nil())
//  def reverse0(list1: IntList, list2: IntList) : IntList = list1 match {
//    case Nil() => list2
//    case Cons(x, xs) => reverse0(xs, Cons(x, list2))
//  }
//
//  def concat(list1: IntList, list2: IntList) : IntList = concat0(list1, list2, Nil())
//  def concat0(list1: IntList, list2: IntList, list3: IntList) : IntList = list1 match {
//    case Nil() => list2 match {
//      case Nil() => reverse(list3)
//      case Cons(y, ys) => concat0(Nil(), ys, Cons(y, list3))
//    }
//    case Cons(x, xs) => concat0(xs, list2, Cons(x, list3))
//  }
}
