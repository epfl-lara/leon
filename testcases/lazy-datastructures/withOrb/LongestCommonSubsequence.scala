package wihtOrb

import leon._
import mem._
import lang._
import annotation._
import com.sun.xml.internal.bind.v2.runtime.reflect.Lister.Pack
import instrumentation._
import invariant._

object LongestCommonSubsequence {

  // data-structure and it's methods
  sealed abstract class Word {
    val size: BigInt = {
      this match {
        case Cons(_, tail) => 1 + tail.size
        case Nil() => BigInt(0)
      }
    } ensuring(_ >= 0)
  }
  case class Cons(x: BigInt, tail: Word) extends Word {
    @ignore
    override def toString: String = {
      if(tail == Nil()) x.toString
      else x.toString + tail.toString
    }
  }
  case class Nil() extends Word {
    @ignore
    override def toString = ""
  }

  val string1 = Cons(1, Cons(2, Cons(2, Cons(3, Nil()))))
  val string2 = Cons(1, Cons(2, Cons(3, Cons(4, Nil()))))

  var xstring = Array[String]()
  var ystring = Array[String]()
  @extern
  def lookup(i: BigInt, j: BigInt) = {
    (xstring(i.toInt), ystring(j.toInt))
  } ensuring(_ => time <= 1)


  // deps and it's lemmas
  def deps(i: BigInt, j: BigInt): Boolean = {
    require(i >= 0 && j >= 0)
        if (i <= 0 || j <= 0) true //deps(i, j - 1)
        //else if(j <= 0) deps(i - 1, j)
        else lcs(i-1, j).cached && lcs(i, j - 1).cached && lcs(i - 1, j - 1).cached  //deps(i - 1, j) && deps(i, j - 1)
  }

  @traceInduct
  def depsMono(i: BigInt, j:BigInt, st1: Set[Fun[BigInt]], st2: Set[Fun[BigInt]]) = {
    require(i >= 0 && j >= 0)
    (st1.subsetOf(st2) && (deps(i, j) withState st1)) ==> (deps(i, j) withState st2)
  } holds
//
//  // FIXME: Is this even needed? (more lemmas shouldn't hurt though)
//  @traceInduct
//  def depsLem(i: BigInt, j: BigInt) = {
//    require(i >= 0 && j >= 0)
//    (i <= j && deps(j, X, Y)) ==> deps(i, X, Y)
//  } holds


  /*def fill(i: BigInt, j: BigInt): Word = {
    require((n ==0 || (n > 0 && deps(n - 1, X, Y))))
    // Knapsack has a bigger requires here
    currX match {
      case Cons(xj, tailx) => {
        currY match {
          case Cons(yi, taily) => {
            if (yi == xj)
              Cons(xj, lcs(n - 1, tailx, taily))
            else {
              val s1 = lcs(n - 1, currX, taily)
              val s2 = fillithRow(X, Y, n, tailx, currY)
              if (s1.size >= s2.size) s1 else s2
            }
          }
          case Nil() => Nil()
        }
      }
      case Nil() => Nil()
    }
  } ensuring(_ => time <= ? * currX.size + ?)*/

  @invstate
  @memoize
  def lcs(i: BigInt, j: BigInt): BigInt = {
  require (i >= 0 && j >= 0 && deps (i, j))
  if (i == 0 || j == 0) BigInt(0)
  else {
  val (xi, yj) = lookup(i, j)
  if (xi == yj)
    lcs (i - 1, j - 1) + 1
  else {
  val s1 = lcs (i - 1, j)
  val s2 = lcs (i, j - 1)
  if (s1 >= s2) s1 else s2
}
}
} ensuring(_ => time <= ?)

  def invoke(i: BigInt, j: BigInt) = {
    require(i >= 0 && j >= 0 && deps(i, j))
    lcs(i, j)
  } ensuring (res => {
    depsMono(i, j, inState[BigInt], outState[BigInt]) && // lemma inst
      deps(i, j) &&
      time <= ?
  })

  def bottomup(m: BigInt, n: BigInt): BigInt = {
    require(m >= 0 && n >= 0) //&& deps(i, j))
    if(m == 0 || n == 0)  BigInt(0)
    else {
      bottomup(m - 1, n) match {
        case _ =>
          bottomup(m, n - 1) match {
            case _ =>
              invoke(m, n)
          }
      }
    }
  } //ensuring(_ = //deps(m, n))

  /*def lcsSol(X: Word, Y: Word) = {
    require(Y.size >= 0 && X.size <= 10) // the second requirement is only to keep the bounds linear
    bottomup(0, Y.size, X, Y)
  } ensuring(_ => time <= ? * Y.size + ?)

  @ignore
  def main(args: Array[String]) {
    import scala.util.Random
    // TODO: Use randomised test cases
    val common = lcsSol(string1, string2)
    println("Common substring of " + string1.toString + " and " + string2.toString + " is " + common.toString)
  }*/
}














