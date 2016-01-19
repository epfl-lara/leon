import leon.lazyeval._
import leon.lazyeval.$._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
//import leon.invariant._

object Knapscak {
  sealed abstract class IList
  case class Cons(x: BigInt, tail: IList) extends IList
  case class Nil() extends IList

  def depsEval(i: BigInt, items: IList): Boolean = {
    require(i >= 0)
    if (i <= 0) true
    else {
      knapSack(i, items).isCached && depsEval(i - 1, items)
    }
  }

  @traceInduct
  def depsEvalMono(i: BigInt, items: IList, st1: Set[$[BigInt]], st2: Set[$[BigInt]]) = {
    require(i >= 0)
    (st1.subsetOf(st2) && (depsEval(i, items) withState st1)) ==> (depsEval(i, items) withState st2)
  } holds

  def maxValue(items: IList, w: BigInt, currList: IList): BigInt = {
    require(w >= 0 && (w == 0 || depsEval(w - 1, items)))
    currList match {
      case Cons(wi, tail) =>
        val oldMax = maxValue(items, w, tail)
        if (wi <= w && wi > 0) {
          val choiceVal = wi + knapSack(w - wi, items)
          if (choiceVal >= oldMax)
            choiceVal
          else
            oldMax
        } else oldMax
      case Nil() => BigInt(0)
    }
  }

  @memoize
  def knapSack(w: BigInt, items: IList): BigInt = {
    require(w >= 0 && (w == 0 || depsEval(w - 1, items)))
    if (w == 0) BigInt(0)
    else {
      maxValue(items, w, items)
    }
  }

  def invoke(i: BigInt, items: IList) = {
    require(i == 0 || (i > 0 && depsEval(i - 1, items)))
    knapSack(i, items)
  } ensuring (res => {
    val in = $.inState[BigInt]
    val out = $.outState[BigInt]
    depsEvalMono(i - 1, items, in, out) &&
      depsEval(i - 1, items)
  })

  def bottomup(i: BigInt, w: BigInt, items: IList): IList = {
    require(w >= 0 &&
      (i == 0 || (i > 0 && depsEval(i - 1, items))))
    val ri = invoke(i, items)
    if (i == w)
      Cons(ri, Nil())
    else {
      Cons(ri, bottomup(i + 1, w, items))
    }
  }
}
