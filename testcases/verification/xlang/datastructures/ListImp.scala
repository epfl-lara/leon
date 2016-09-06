import leon.lang._

object ListImp {

  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def content(l: List) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }

  def size(l: List) : Int = {
    var r = 0
    (while(!l.isInstanceOf[Nil]) {
      r = r+1
    }) invariant(r >= 0)
    r
  } ensuring(res => res >= 0)

  def reverse(l: List): List = {
    var r: List = Nil()
    var l2: List = l

    (while(!l2.isInstanceOf[Nil]) {
      val Cons(head, tail) = l2
      l2 = tail
      r = Cons(head, r)
    }) invariant(content(r) ++ content(l2) == content(l))

    r
  } ensuring(res => content(res) == content(l))

  def append(l1 : List, l2 : List) : List = {
    var r: List = l2
    var tmp: List = reverse(l1)

    (while(!tmp.isInstanceOf[Nil]) {
      val Cons(head, tail) = tmp
      tmp = tail
      r = Cons(head, r)
    }) invariant(content(r) ++ content(tmp) == content(l1) ++ content(l2))

    r
  } ensuring(content(_) == content(l1) ++ content(l2))


}
