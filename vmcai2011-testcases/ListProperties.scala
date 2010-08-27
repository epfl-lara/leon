import scala.collection.immutable.Set

object IntListProperties {
  sealed abstract class IntList
  case class Cons(head: Int, tail: IntList) extends IntList
  case class Nil() extends IntList

  case class IntListPair(left: IntList, right: IntList)

  // some uninterpreted predicate on integers
  def p(i: Int) : Boolean = { throw new Exception("Uninterpreted.") }

  def size(list: IntList) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  // proved with unrolling = 1
  def content(list: IntList) : Set[Int] = (list match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }) ensuring(_.size <= size(list))

  // should be proved with unrolling = 1
  def filter(list: IntList) : IntList = (list match {
    case Nil() => Nil()
    case Cons(x, xs) => {
      val rest = filter(xs)
      if(p(x)) Cons(x, rest) else rest
    }
  }) ensuring(res => content(res).size <= (content(list)).size)

//  def removeDuplicates(list: IntList) : IntList = (list match {
//    case Nil() => Nil()
//    case Cons(x, xs) => Cons(x, removeDuplicates(removeFrom(x, xs)))
//  }) ensuring(newList => content(newList) == content(list))
//
//  // proved with unrolling = 1 (but sloooooooow)
//  def removeFrom(v: Int, list: IntList) : IntList = (list match {
//    case Nil() => Nil()
//    case Cons(x, xs) => {
//      val rest = removeFrom(v, xs)
//      if(v == x) rest else Cons(x, rest)
//    }
//  }) ensuring(newList => content(newList) == content(list) -- Set(v))
//
//  // proved with unrolling = 1
//  def occurCount(v: Int, list: IntList) : Int = (list match {
//    case Nil() => 0
//    case Cons(x, xs) => {
//      (if(x == v) 1 else 0) + occurCount(v, xs)
//    }
//  }) ensuring(count => count >= 0 && (count > 0) == content(list).contains(v))
//
//  // proved with unrolling = 1
//  def occurs(v: Int, list: IntList) : Boolean = (list match {
//    case Nil() => false
//    case Cons(x, xs) => if(x == v) true else occurs(v, xs)
//  }) ensuring(_ == content(list).contains(v))
}
