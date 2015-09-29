import leon.instrumentation._
import leon.invariant._
import leon.annotation._

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
  } ensuring(res => true && tmpl((a,b,c,d,e) => depth <= a*((k+1)*(length(s1) + length(s2))) + b*size(str1) + e))

  def max(x: BigInt, y: BigInt) : BigInt = if(x >= y) x else y

  //Fig. 2 of Speed POPL'09
  def Dis1(x : BigInt, y : BigInt, n: BigInt, m: BigInt) : BigInt = {
    if(x >= n) 0
    else {
      if(y < m) Dis1(x, y+1, n, m)
      else Dis1(x+1, y, n, m)
    }
  } ensuring(res => true && tmpl((a,b,c) => depth <= a*max(0,n-x) + b*max(0,m-y) + c))

  //Fig. 2 of Speed POPL'09
  def Dis2(x : BigInt, z : BigInt, n: BigInt) : BigInt = {
    if(x >= n) 0
    else {
      if(z > x) Dis2(x+1, z, n)
      else Dis2(x, z+1, n)
    }
  } ensuring(res => true && tmpl((a,b,c) => depth <= a*max(0,n-x) + b*max(0,n-z) + c))

  //Pg. 138, Speed POPL'09
  def Dis3(x : BigInt, b : Boolean, t: BigInt, n: BigInt) : BigInt = {
    require((b && t == 1) || (!b && t == -1))
    if(x > n || x < 0) 0
    else {
      if(b) Dis3(x+t, b, t, n)
      else Dis3(x-t, b, t, n)
    }
  } ensuring(res => true && tmpl((a,c) => depth <= a*max(0,(n-x)) + c))

  //Pg. 138, Speed POPL'09
  def Dis4(x : BigInt, b : Boolean, t: BigInt, n: BigInt) : BigInt = {
    if(x > n || x < 0) 0
    else {
      if(b) Dis4(x+t, b, t, n)
      else Dis4(x-t, b, t, n)
    }
  } ensuring(res => true && tmpl((a,c,d,e) => (((b && t >= 0) || (!b && t < 0)) && depth <= a*max(0,(n-x)) + c)
  					|| (((!b && t >= 0) || (b && t < 0)) && depth <= d*max(0,x) + e)))
}
