package ks

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._

/**
* Knapsack dynamic programming algorithm.
* Written in a purely functional way using memoization.
*/
object Knapscak {
  
  sealed abstract class IList { // a list of pairs: (weight, value)
    def size: BigInt = {
      this match {
        case Cons(_, tail) => 1 + tail.size
        case Nil()         => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  case class Cons(x: (BigInt, BigInt), tail: IList) extends IList { 
    @ignore
    override def toString: String = {
      if(tail == Nil()) x.toString
      else x.toString + "," + tail.toString
    }
  }
  case class Nil() extends IList {
    @ignore
    override def toString = ""
  }
  
  /**
   * A property that holds if the `solveForWeight` 
   *  is cached for all weights lesser than or equal to `i`.
   */
  def deps(i: BigInt, items: IList): Boolean = {
    require(i >= 0)
    cached(solveForWeight(i, items)) &&
      (if (i <= 0) true
      else {
        deps(i - 1, items)
      })
  }

  // Monotonicity of deps with respect to the state
  @invisibleBody
  @traceInduct
  def depsMono(i: BigInt, items: IList, st1: Set[Fun[BigInt]], 
      st2: Set[Fun[BigInt]]) = {
    require(i >= 0)
    (st1.subsetOf(st2) && 
      (deps(i, items) in st1)) ==> (deps(i, items) in st2)
  } holds

  // $\forall$. x, x $\le$ y && deps(y) $\implies$ deps(x)
  @traceInduct
  def depsLem(x: BigInt, y: BigInt, items: IList) = {
    require(x >= 0 && y >= 0)
    (x <= y && deps(y, items)) ==> deps(x, items)
  } holds

  /**
   * Computes the optimal value of filling a knapsack of 
   * weight `w` using `items`
   */
  @memoize
  def solveForWeight(w: BigInt, items: IList): BigInt = {
    require(w >= 0 && (w == 0 || deps(w - 1, items)))
    if (w == 0) BigInt(0)
    else {
      maxOverItems(items, w, items)
    }
  } ensuring (_ => alloc <= ?)

  /**
   * Computes the optimal value of filling a knapsack of 
   * weight `w` using `remItems`
   */
  @invstate
  def maxOverItems(items: IList, w: BigInt, 
      remItems: IList): BigInt = {
    require((w == 0 || (w > 0 && deps(w - 1, items))) &&
      // lemma inst
      (remItems match {
        case Cons((wi, vi), _) =>
          if (wi <= w && wi > 0)
             depsLem(w - wi, w - 1, items)
          else true
        case Nil() => true
      }))
    remItems match {
      case Cons((wi, vi), tail) =>
        val maxWithoutItem = maxOverItems(items, w, tail)
        if (wi <= w && wi > 0) {
          val maxWithItem = 
            vi + solveForWeight(w - wi, items)
          if (maxWithItem >= maxWithoutItem)
            maxWithItem
          else
            maxWithoutItem
        } else
          maxWithoutItem
      case Nil() => BigInt(0)
    }
  } ensuring (_ => alloc <= ?)

  /**
   * A helper function that specifies properties ensured by 
   * an invocation of `solveForWeight`.
   */
  @invisibleBody
  def solveForWeightHelper(i: BigInt, items: IList) = {
    require(i == 0 || (i > 0 && deps(i - 1, items)))
    solveForWeight(i, items)
  } ensuring (res => {
    (i == 0 || 
      depsMono(i - 1, items, inSt[BigInt], outSt[BigInt])) && 
      deps(i, items) &&
      alloc <= ? 
  })

  // Computes the optimal solution for all weights upto `w`.
  def solveUptoWeight(w: BigInt, items: IList): IList = {
    require(w >= 0)
    if (w == 0)
      Cons((w, solveForWeightHelper(w, items)), Nil())
    else {
      val tail = solveUptoWeight(w - 1, items)
      Cons((w, solveForWeightHelper(w, items)), tail)
    }
  } ensuring { _ => deps(w, items) &&
  alloc <= ? * w + ?
  }

  // Computes the list of optimal solutions 
  // for all weights up to `w`
  def knapsack(w: BigInt, items: IList) = {
    require(w >= 0)
    solveUptoWeight(w, items)
  } ensuring {_ => 
   alloc <= ? * w + ?
  }

  @ignore
  def main(args: Array[String]) {
    import scala.util.Random
    // pick some random weights and values
    val input1 = (1 to 10).foldRight(Nil(): IList) {
      case (i, acc) => Cons((i, i), acc)
    }
    val reslist1 = knapsack(100, input1) 
    //exponential without memoization
    println("Optimal solutions: " + reslist1.toString)
    
    val l = ((1 to 10) zip (10 to 1 by -1))
    val input2 = l.foldRight(Nil(): IList) {
      case ((i, j), acc) => Cons((i, j), acc)
    }
    val reslist2 = knapsack(100, input2)
    println("Optimal solutions for set 2: " + reslist2.toString)
  }
}
