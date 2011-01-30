object List1 {
  import funcheck.Utils._

  sealed abstract class MyList
  case class Cons(head: Int, tail: MyList) extends MyList
  case class Nil() extends MyList

  def size(list: MyList) : Int = list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }

  def sizeTR(list: MyList, acc: Int) : Int = (list match {
    case Nil() => acc
    case Cons(_, xs) => sizeTR(xs, 1 + acc)
  }) ensuring(_ == size(list) + acc)

  def prop(list: MyList) : Boolean = {
    size(list) == sizeTR(list, 0)
  } ensuring(res => res)
  //} holds
}
