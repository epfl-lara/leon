package withOrb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._
import collection._

// DO NOT remove the commented code, lemmas are hard to come up with :-)

/**
 * Implementation of the Viterbi algorithm 
 * Wiki - https://en.wikipedia.org/wiki/Viterbi_algorithm
 * The probabilities are in logarithms.
 */
object Viterbi {

  @ignore
  var xstring = Array[BigInt]()
  @ignore
  var ystring = Array[BigInt]()
  /**
   * Observation space, O
   */
  @extern
  def O(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)
  /**
   * State space, S
   */
  @extern
  def S(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)
  /** 
   * Let K be the size of the state space. Then the transition matrix
   * A of size K * K such that A_{ij} stores the transition probability 
   * of transiting from state s_i to state s_j
   */
  @extern
  def A(i: BigInt, j: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)
  /**
   * Let N be the size of the observation space. Emission matrix B of 
   * size K * N such that B_{ij} stores the probability of observing o_j 
   * from state s_i
   */
  @extern
  def B(i: BigInt, j: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)
  /**
   * An array of initial probabilities C of size K such that C_i stores 
   * the probability that x_1 == s_i 
   */
  @extern
  def C(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)
  /**
   * Generated observations, Y
   */
  @extern
  def Y(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)

  // deps and it's lemmas
  // def deps(j: BigInt, K: BigInt): Boolean = {
  //   require(j >= 0 && K >= 0)
  //   if(j <= 0) true
  //   else viterbiCached(0, j - 1, K)
  // }

  // def viterbiCached(l: BigInt, j: BigInt, K: BigInt): Boolean = {
  //   require(l >= 0 && j >= 0 && K >= l)
  //   viterbi(l, j, K).cached && {
  //   if(l == K) true
  //   else viterbiCached(l + 1, j, K)} 
  // }

  def deps(j: BigInt, K: BigInt): Boolean = {
    require(j >= 0 && K >= 0)
    if(j <= 0) true
    else viterbiCached(K, j - 1, K)
  }

  def viterbiCached(l: BigInt, j: BigInt, K: BigInt): Boolean = {
    require(l >= 0 && j >= 0 && K >= l)
    viterbi(l, j, K).cached && {
    if(l <= 0 && j <= 0) true
    else if(l <= 0) viterbiCached(l, j - 1, K)
    else if(j <= 0) viterbiCached(l - 1, j, K)
    else viterbiCached(l - 1, j, K) && viterbiCached(l, j - 1, K)} 
  }

  // def cachedLem(l: BigInt, j: BigInt, K: BigInt): Boolean = {
  //   require(j >= 0 && l >= 0 && K >= l)
  //   (if(l == K) true
  //     else if(l == 0) cachedLem(l + 1, j, K)
  //     else cachedLem(l + 1, j, K) && cachedLem(l - 1, j, K)
  //     ) && (viterbiCached(K, j, K) ==> viterbiCached(l, j, K))    
  // } holds

  @traceInduct
  def cachedLem(l: BigInt, j: BigInt, K: BigInt): Boolean = {
    require(j >= 0 && l >= 0 && K >= l)
    (l <= K && viterbiCached(K, j, K)) ==> viterbiCached(l, j, K)    
  } holds

  @traceInduct
  def depsMono(j: BigInt, K: BigInt, st1: Set[Fun[BigInt]], st2: Set[Fun[BigInt]]) = {
    require(j >= 0 && K >= 0)
    (st1.subsetOf(st2) && (deps(j, K) withState st1)) ==> (deps(j, K) withState st2)
  } holds

  @invstate
  def fillEntry(l: BigInt, i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 1 && l >= 0 && K >= l && K >= i && deps(j, K) && cachedLem(l, j - 1, K))
    val a1 = viterbi(l, j - 1, K) + A(l, i) + B(i, Y(j))
    if(l == K) a1
    else {
      val a2 = fillEntry(l + 1, i, j, K) // have a look at the algo again @Sumith
      if(a1 > a2) a1 else a2
    }
  } ensuring(time <= ? * (K - l) + ?)

  @invstate
  @memoize
  def viterbi(i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 0 && K >= i && (j == 0 || j > 0 && deps(j, K)))
    if(j == 0) {
      C(i) + B(i, Y(0))
    } else {
      fillEntry(0, i, j, K)
    }
  } ensuring(time <= ? * K + ?)

  @invisibleBody
  def invoke(i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 0 && K >= i && (j == 0 || j > 0 && deps(j, K)))
    viterbi(i, j, K)
  } ensuring(res => {
    val in = inState[BigInt]
    val out = outState[BigInt]
    (j == 0 || depsMono(j, K, in, out)) && deps(j, K) && time <= ? * K + ?
  })

  @invisibleBody
  def fillColumn(i: BigInt, j: BigInt, K: BigInt): List[BigInt] = {
    require(i >= 0 && j >= 0 && K >= i)
    if(i == K) {
      Cons(invoke(i, j, K), Nil[BigInt]())
    }
    else {
      val tail = fillColumn(i + 1, j, K)
      Cons(invoke(i, j, K), tail)
    }
  } ensuring(time <= ? * ((K - i) * K) + ? * K + ?)

  @invisibleBody
  def fillTable(j: BigInt, T: BigInt, K: BigInt): List[List[BigInt]] = {
    require(j >= 0 && T >= j && K >= 0)
    if(j == T) {
      Cons(fillColumn(0, j, K), Nil[List[BigInt]]())
    }
    else {
      val tail = fillTable(j + 1, T, K)
      Cons(fillColumn(0, j, K), tail)
    }
  } ensuring(time <= ? *((K * K) * (T - j)) + ? * ((T - j)*K) + ? * (T - j) + ? * (K*K) + ? * K + ?)

  def viterbiSols(T: BigInt, K: BigInt): List[List[BigInt]] = {
    require(T >= 0 && K >= 0)
    fillTable(0, T, K)
  } ensuring(time <= ? * ((K * K) * T) + ? * ((T)*K) + ? * T + ? * (K*K) + ? * K + ?)

}
