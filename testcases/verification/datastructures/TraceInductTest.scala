import leon.annotation._
import leon.lang._
import leon.collection._

object TraceInductTest {
  sealed abstract class IList
  case class ICons(head: BigInt, tail: IList) extends IList
  case class INil() extends IList

  // proved with unrolling=0
  def size(l: IList): BigInt = (l match {
    case INil()      => BigInt(0)
    case ICons(_, t) => 1 + size(t)
  }) //ensuring(res => res >= 0)

  @traceInduct
  def nonNegSize(l: IList): Boolean = {
    size(l) >= 0
  } holds

  def reverse0(l1: IList, l2: IList): IList = (l1 match {
    case INil()       => l2
    case ICons(x, xs) => reverse0(xs, ICons(x, l2))
  })

  def content(l: IList): Set[BigInt] = l match {
    case INil()       => Set.empty[BigInt]
    case ICons(x, xs) => Set(x) ++ content(xs)
  }
  
  @traceInduct("reverse0")
  def revPreservesContent(l1: IList, l2: IList): Boolean = {
    content(l1) ++ content(l2) == content(reverse0(l1, l2))
  } holds  
    
  def insertAtIndex[T](l: List[T], i: BigInt, y: T): List[T] = {
    require(0 <= i && i <= l.size)
    l match {
      case Nil() =>
        Cons[T](y, Nil())
      case _ if i == 0 =>
        Cons[T](y, l)
      case Cons(x, tail) =>
        Cons[T](x, insertAtIndex(tail, i - 1, y))
    }
  }

  // A lemma about `append` and `insertAtIndex`
  @traceInduct("insertAtIndex")
  def appendInsertIndex[T](l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i <= l1.size + l2.size)
      (insertAtIndex((l1 ++ l2), i, y) == (
        if (i < l1.size) insertAtIndex(l1, i, y) ++ l2
        else l1 ++ insertAtIndex(l2, (i - l1.size), y)))
  }.holds
  
  def power(x: BigInt, y: BigInt) : BigInt = {
    require(y >= 0 && x >= 1)
    if(y < 1) BigInt(1)
    else
      x * power(x, y - 1)
  } ensuring(_ >= 1)
  
  @traceInduct
  def powerMonotone(x1: BigInt, x2: BigInt, y: BigInt) = {
    require(y >= 0)
    (1 <= x1 && x1 <= x2) ==> power(x1, y) <= power(x2, y)
  } holds
}
