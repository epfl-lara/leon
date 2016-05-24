package wihtOrb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._
import collection._

object LongestCommonSubsequence {

  // data-structure and it's methods
  sealed abstract class Word {
    val size: BigInt = {
      this match {
        case Cons(_, tail) => 1 + tail.size
        case Nil()         => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  case class Cons(x: BigInt, tail: Word) extends Word {
    @ignore
    override def toString: String = {
      if (tail == Nil()) x.toString
      else x.toString + tail.toString
    }
  }
  case class Nil() extends Word {
    @ignore
    override def toString = ""
  }

  val string1 = Cons(1, Cons(2, Cons(2, Cons(3, Nil()))))
  val string2 = Cons(1, Cons(2, Cons(3, Cons(4, Nil()))))

  @ignore
  var xstring = Array[BigInt]()
  @ignore
  var ystring = Array[BigInt]()
  @extern
  def lookup(i: BigInt, j: BigInt) = {
    (xstring(i.toInt), ystring(j.toInt))
  } ensuring (_ => time <= 1)

  // deps and it's lemmas
  def deps(i: BigInt, j: BigInt): Boolean = {
    require(i >= 0 && j >= 0)
    lcs(i, j).cached &&
      (if (i <= 0 && j <= 0) true
      else if (i <= 0) deps(i, j - 1)
      else if (j <= 0) deps(i - 1, j)
      else deps(i - 1, j) && deps(i, j - 1))
  }

  @invisibleBody
  @traceInduct
  def depsMono(i: BigInt, j: BigInt, st1: Set[Fun[BigInt]], st2: Set[Fun[BigInt]]) = {
    require(i >= 0 && j >= 0)
    (st1.subsetOf(st2) && (deps(i, j) withState st1)) ==> (deps(i, j) withState st2)
  } holds

  @traceInduct
  def depsLem(i: BigInt, j: BigInt, m: BigInt, n: BigInt) = {
    require(i >= 0 && j >= 0 && m >= 0 && n >= 0)
    (i <= m && j <= n && deps(m, n)) ==> deps(i, j)
  } holds

  @invstate
  @memoize
  @invisibleBody
  def lcs(i: BigInt, j: BigInt): BigInt = {
    require((i >=0 && j >= 0) && (i == 0 || deps(i - 1, j)) && (j == 0 || deps(i, j-1)))
    if (i == 0 || j == 0) BigInt(0)
    else {
      val (xi, yj) = lookup(i, j)
      if (xi == yj)
        lcs(i - 1, j - 1) + 1
      else {
        val s1 = lcs(i - 1, j)
        val s2 = lcs(i, j - 1)
        if (s1 >= s2) s1 else s2
      }
    }
  } ensuring (_ => time <= ?)

  @invisibleBody
  def invoke(i: BigInt, j: BigInt, n: BigInt) = {
    require((i >=0 && j >= 0 && n >= j) && (i == 0 || deps(i - 1, j)) && (j == 0 || deps(i, j-1)))
    lcs(i, j)
  } ensuring (res => {
    val in = inState[BigInt]
    val out = outState[BigInt]
      (i == 0 || (depsMono(i - 1, j, in, out) && depsMono(i - 1, n, in, out))) &&
      (j == 0 || depsMono(i, j - 1, in, out)) &&
      deps(i, j) &&
      time <= ?
  })

  /**
   * Given a m x n DP problem, the following function solves the subproblems by traversing the problem space
   * from right to left, and bottom to top.
   * @param m - number of rows remaining
   * @param n - max. number of columns
   * @param j - number of columns remaining
   */
  def bottomup(m: BigInt, j: BigInt, n: BigInt): BigInt = {
    require(0 <= m && 0 <= j && j <= n)
    if (m == 0 && j == 0) {
      invoke(m, j, n)
    }
    else if(j == 0) {
      bottomup(m - 1, n, n) match {
        case _ => invoke(m, j, n)
      }
    }
    else {
      bottomup(m, j - 1, n) match {
        case _ => invoke(m, j, n)
      }
    }
  } ensuring {_ =>
    bottomUpPost(m, j, n) &&
      time <= ? * (m * n)  + ? * m + ? * j + ?
   }

  @invisibleBody
  def bottomUpPost(m: BigInt, j: BigInt, n: BigInt): Boolean = {
    require(m >= 0 && n >= j && j >= 0)
    (m == 0 || (deps(m - 1, n) && depsLem(m - 1, j, m - 1, n))) && deps(m, j) &&
      depsLem(m, 0, m, j)
  }

  /*def lcsSol(X: Word, Y: Word) = {
    require(Y.size >= 0 && X.size <= 10) // the second requirement is only to keep the bounds linear
    bottomup(0, Y.size, X, Y)
  } ensuring(_ => time <= ? * Y.size + ?)*/

  /*@ignore
  def main(args: Array[String]) {
    import scala.util.Random
    // TODO: Use randomised test cases
    val common = lcsSol(string1, string2)
    println("Common substring of " + string1.toString + " and " + string2.toString + " is " + common.toString)
  }*/
}
