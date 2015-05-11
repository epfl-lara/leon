
import leon._
import leon.lang._
import leon.collection._

sealed abstract class Queue[T] {

   def size: BigInt = {
      this match {
         case QEmpty() => 0
         case QCons(f, r) => f.size + r.size
      }
   } ensuring (res => res == this.toList.size && res >= 0)

   def toList: List[T] = (this match {
      case QEmpty() => Nil()
      case QCons(f, r) => f ++ r.reverse
   }) ensuring (resOne => this.content == resOne.content && resOne.size >= 0)

   def content: Set[T] = this match {
      case QEmpty() => Set()
      case QCons(f, r) => f.content ++ r.content
   }
}

case class QCons[T](f : List[T], r: List[T]) extends Queue[T]
case class QEmpty[T]() extends Queue[T]
