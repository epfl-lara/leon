package lcs

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._
import collection._

/**
* A memoized implementation of computing the length of the 
* longest common subsequence between two sequences. Here, 
* the sequences are represented as integer arrays
* whose elements can be looked up in unit time and zero memory allocations.
* The lookup function is not verified by the algorithm (and so is marked as @extern),
* as it uses mutable variables and arrays. 
* Rest of the implementation for computing the optimal length using a recurrence 
* relation is purely functional and uses memoization.
**/
object LongestCommonSubsequence {

  @ignore
  var xstring = Array[BigInt]()
  @ignore
  var ystring = Array[BigInt]()
  @extern
  def lookup(i: BigInt, j: BigInt) = {
    (xstring(i.toInt), ystring(j.toInt))
  } ensuring (_ => alloc <= 0)

  // deps and it's lemmas
  def deps(i: BigInt, j: BigInt): Boolean = {
    require(i >= 0 && j >= 0)
    cached(lcs(i, j)) &&
      (if (i <= 0 && j <= 0) true
      else if (i <= 0) deps(i, j - 1)
      else if (j <= 0) deps(i - 1, j)
      else deps(i - 1, j) && deps(i, j - 1))
  }

  @invisibleBody
  @traceInduct
  def depsMono(i: BigInt, j: BigInt, st1: Set[Fun[BigInt]], st2: Set[Fun[BigInt]]) = {
    require(i >= 0 && j >= 0)
    (st1.subsetOf(st2) && (deps(i, j) in st1)) ==> (deps(i, j) in st2)
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
  } ensuring (_ => alloc <= ?)

  @invisibleBody
  def invoke(i: BigInt, j: BigInt, n: BigInt) = {
    require((i >=0 && j >= 0 && n >= j) && (i == 0 || deps(i - 1, j)) && (j == 0 || deps(i, j-1)))
    lcs(i, j)
  } ensuring (res => {
    val in = inSt[BigInt]
    val out = outSt[BigInt]
      (i == 0 || (depsMono(i - 1, j, in, out) && depsMono(i - 1, n, in, out))) &&
      (j == 0 || depsMono(i, j - 1, in, out)) &&
      deps(i, j) &&
      alloc <= ?
  })

  /**
   * Given a m x n DP problem, the following function solves the subproblems by traversing the problem space
   * from right to left, and bottom to top.
   * @param m - number of rows remaining
   * @param n - max. number of columns
   * @param j - number of columns remaining (initially set to n)
   * @result returns a list of solutions for each sub-problem (the size of the resulting list will be quadratic)
   */
  def bottomup(m: BigInt, j: BigInt, n: BigInt): List[BigInt] = {
    require(0 <= m && 0 <= j && j <= n)
    if (m == 0 && j == 0) {
      Cons(invoke(m, j, n), Nil[BigInt]())
    }
    else if(j == 0) {
      val tail = bottomup(m - 1, n, n)
      Cons(invoke(m, j, n), tail)
    }
    else {
      val tail = bottomup(m, j - 1, n)
      Cons(invoke(m, j, n), tail)
    }
  } ensuring {_ =>
    bottomUpPost(m, j, n) &&
      alloc <= ? * (m * n)  + ? * m + ? * j + ?
   }

  @invisibleBody
  def bottomUpPost(m: BigInt, j: BigInt, n: BigInt): Boolean = {
    require(m >= 0 && n >= j && j >= 0)
    (m == 0 || (deps(m - 1, n) && (j == n || depsLem(m - 1, j + 1, m - 1, n)))) && deps(m, j) &&
      depsLem(m, 0, m, j)
  }

  /**
  * The returned list has the solution to all the sub-problems of the dynammic progamming 
  * algrithm. Its size if quadratic in this case. 
  * The length of the longest common subsequence between the sequences: xstring of length m and 
  * ystring of length n is given by first entry of the returned list.  
  **/
  def lcsSols(m: BigInt, n: BigInt): List[BigInt] = {
    require(0 <= m && 0 <= n)
    bottomup(m, n, n)
  } ensuring(_ => alloc <= ? * (m * n)  + ? * m + ? * n + ?)

}
