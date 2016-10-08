package prims

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import instrumentation._
import invariant._
import collection._

/**
 * The running example shown in Fig. 1 of the paper.
 * The function creates an infinite stream of numbers that flagged if they are prime.
 */
object PrimeStream {

  sealed abstract class Bool
  case class True() extends Bool
  case class False() extends Bool

  sealed abstract class Stream
  private case class SCons(x: (BigInt, Bool), tailFun: () => Stream) extends Stream {
    lazy val tail = tailFun()
  }
  private case class SNil() extends Stream

  private val primeStream = {
    SCons((1, True()), () => nextElem(BigInt(2)))
  }

  def isPrimeRec(i: BigInt, n: BigInt): Bool = {
    require(i >= 1 && i < n)
    if(i == 1) True()
    else if((n / i) * i == n) False()
    else isPrimeRec(i - 1, n)
  } ensuring(_ => alloc <= ?)

  def isPrimeNum(n: BigInt): Bool = {
    require(n >= 2)
    isPrimeRec(n -1, n)
  } ensuring(r => alloc <= ?)

  def nextElem(i: BigInt): Stream = {
    require(i >= 2)
    val x = (i, isPrimeNum(i))
    val y = i+1
    SCons(x, () => nextElem(y))
  } ensuring(r => alloc <= ?)

  def isPrimeS(s: Stream, i: BigInt): Boolean = {
    require(i >= 2)
   s match {
     case SNil() => true
     case SCons(x, tfun) => tfun == (() => nextElem(i))
   }}

  def primesUntilN(n: BigInt): List[BigInt] = {
    require(n >= 2)
    takeRec(0, n - 2, primeStream)
  } ensuring {r => concUntil(primeStream, n - 2) && alloc <= ? * n + ?
  }

 def takeRec(i: BigInt, n: BigInt, s: Stream): List[BigInt] = {
  require(0 <= i && i <= n && isPrimeS(s, i + 2))
  s match {
   case c@SCons((x, b), _) =>
     if(i < n) {
       val resTail = takeRec(i + 1, n, c.tail)
       if(b == True())
         Cons(x, resTail)
        else resTail
     }
     else Nil[BigInt]()
   case _ => Nil[BigInt]()
  }
 } ensuring{r => concUntil(s, n - i) && alloc <= ? * (n - i) + ? }

 def concUntil(s: Stream, i: BigInt): Boolean = {
   s match {
     case c: SCons =>
       if(i > 0) cached(c.tail) && concUntil(c.tail*, i - 1)
       else true
     case _ => true
   }
 }
}
