import leon.invariant._
import leon.instrumentation._
import leon.math._

object SpeedBenchmarks {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  def size(l: List): BigInt = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  })

  sealed abstract class StringBuffer
  case class Chunk(str: List, next: StringBuffer) extends StringBuffer
  case class Empty() extends StringBuffer

  def length(sb: StringBuffer) : BigInt = sb match {
    case Chunk(_, next) => 1 + length(next)
    case _ => 0
  }

  def sizeBound(sb: StringBuffer, k: BigInt) : Boolean ={
    sb match {
      case Chunk(str, next) => size(str) <= k && sizeBound(next, k)
      case _ => 0 <= k
    }
  }

  def sizeBuffer(sb: StringBuffer): BigInt = {
    sb match {
      case Chunk(str, next) => size(str) + sizeBuffer(sb)
      case Empty() => 0
    }
  }

  /**
   * Fig. 1 of SPEED, POPL'09: The functional version of the implementation.
   * Equality check of two string buffers
   */
  def Equals(str1: List, str2: List, s1: StringBuffer, s2: StringBuffer, k: BigInt) : Boolean = {
    require(sizeBound(s1, k) && sizeBound(s2, k) && size(str1) <= k && size(str2) <= k && k >= 0)

    (str1, str2) match {
      case (Cons(h1,t1), Cons(h2,t2)) => {
        if(h1 != h2) false
        else Equals(t1,t2, s1,s2, k)
      }
      case (Cons(_,_), Nil()) => {
        //load from s2
        s2 match {
          case Chunk(str, next) => Equals(str1, str, s1, next, k)
          case Empty() => false
        }
      }
      case (Nil(), Cons(_,_)) => {
        //load from s1
        s1 match {
          case Chunk(str, next) => Equals(str, str2, next, s2, k)
          case Empty() => false
        }
      }
      case _ =>{
        //load from both
        (s1,s2) match {
          case (Chunk(nstr1, next1),Chunk(nstr2, next2)) => Equals(nstr1, nstr2, next1, next2, k)
          case (Empty(),Chunk(nstr2, next2)) => Equals(str1, nstr2, s1, next2, k)
          case (Chunk(nstr1, next1), Empty()) => Equals(nstr1, str2, next1, s2, k)
          case _ => true
        }
      }
    }
  } ensuring(res => tmpl((a,b,c,d,e) => stack <= a*max(sizeBuffer(s1), sizeBuffer(s2)) + c*(k+1) + e))
}
