import leon.Utils._
import leon.Annotations._

object ListOperationsImp {

  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  sealed abstract class IPList
  case class IPCons(head: (Int, Int), tail: IPList) extends IPList
  case class IPNil() extends IPList

  def content(l: List) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }

  def iplContent(l: IPList) : Set[(Int, Int)] = l match {
    case IPNil() => Set.empty[(Int, Int)]
    case IPCons(x, xs) => Set(x) ++ iplContent(xs)
  }

  def size(l: List) : Int = {
    var r = 0
    var l2 = l
    (while(!l2.isInstanceOf[Nil]) {
      val Cons(_, tail) = l2
      l2 = tail
      r = r+1
    }) invariant(r >= 0)
    r
  } ensuring(res => res >= 0)

  def sizeBuggy(l: List) : Int = {
    var r = -1
    var l2 = l
    (while(!l2.isInstanceOf[Nil]) {
      val Cons(_, tail) = l2
      l2 = tail
      r = r+1
    }) invariant(r >= 0)
    r
  } ensuring(res => res >= 0)

  //just to help for specification, makes sense since specification are not executed
  def sizeFun(l: List) : Int = l match {
    case Nil() => 0
    case Cons(_, t) => 1 + sizeFun(t)
  } 
  def iplSizeFun(l: IPList) : Int = l match {
    case IPNil() => 0
    case IPCons(_, t) => 1 + iplSizeFun(t)
  }

  def iplSize(l: IPList) : Int = {
    var r = 0
    var l2 = l
    (while(!l2.isInstanceOf[IPNil]) {
      val IPCons(_, tail) = l2
      l2 = tail
      r = r+1
    }) invariant(r >= 0)
    r
  } ensuring(_ >= 0)

  def sizeStrongSpec(l: List): Int = {
    var r = 0
    var l2 = l
    (while(!l2.isInstanceOf[Nil]) {
      val Cons(head, tail) = l2
      l2 = tail
      r = r+1
    }) invariant(r == sizeFun(l) - sizeFun(l2))
    r
  } ensuring(res => res == sizeFun(l))

  def zip(l1: List, l2: List) : IPList = ({
    require(sizeFun(l1) == sizeFun(l2))
    var  r: IPList = IPNil()
    var ll1: List = l1
    var ll2 = l2

    (while(!ll1.isInstanceOf[Nil]) {
      val Cons(l1head, l1tail) = ll1
      val Cons(l2head, l2tail) = if(!ll2.isInstanceOf[Nil]) ll2 else Cons(0, Nil())
      r = IPCons((l1head, l2head), r)
      ll1 = l1tail
      ll2 = l2tail
    }) invariant(iplSizeFun(r) + sizeFun(ll1) == sizeFun(l1))

    iplReverse(r)
  }) ensuring(res => iplSizeFun(res) == sizeFun(l1))

  def drunk(l : List) : List = {
    var r: List = Nil()
    var l2 = l
    (while(!l2.isInstanceOf[Nil]) {
      val Cons(head, tail) = l2
      l2 = tail
      r = Cons(head, Cons(head, r))
    }) invariant(sizeFun(r) == 2 * sizeFun(l) - 2 * sizeFun(l2))
    r
  } ensuring (sizeFun(_) == 2 * sizeFun(l))


  def iplReverse(l: IPList): IPList = {
    var r: IPList = IPNil()
    var l2: IPList = l

    (while(!l2.isInstanceOf[IPNil]) {
      val IPCons(head, tail) = l2
      l2 = tail
      r = IPCons(head, r)
    }) invariant(iplContent(r) ++ iplContent(l2) == iplContent(l) && iplSizeFun(r) + iplSizeFun(l2) == iplSizeFun(l))

    r
  } ensuring(res => iplContent(res) == iplContent(l) && iplSizeFun(res) == iplSizeFun(l))

  def reverse(l: List): List = {
    var r: List = Nil()
    var l2: List = l

    (while(!l2.isInstanceOf[Nil]) {
      val Cons(head, tail) = l2
      l2 = tail
      r = Cons(head, r)
    }) invariant(content(r) ++ content(l2) == content(l) && sizeFun(r) + sizeFun(l2) == sizeFun(l))

    r
  } ensuring(res => content(res) == content(l) && sizeFun(res) == sizeFun(l))

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
