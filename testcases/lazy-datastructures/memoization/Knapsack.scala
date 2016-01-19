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
    if(i <= 0) true
    else {
      knapSack(i, items).isCached && depsEval(i-1, items)
    }
  }

  def maxValue(items: IList, w: BigInt, currList: IList): BigInt = {
    require(w >= 0)
    currList match {
      case Cons(wi, tail) =>
        val oldMax = maxValue(items, w, tail)
        if (wi <= w) {
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
    require(w >= 0)
    if (w == 0) BigInt(0)
    else {
      maxValue(items, w, items)
    }
  }

  def bottomup(i: BigInt, w: BigInt, items: IList): IList = {
    require(i >= 0 && w >= 0 &&
        (i == 0 || depsEval(i-1, items)))
    if (i == w)
      Cons(knapSack(i, items), Nil())
    else {
      val ri = knapSack(i, items)
      Cons(ri, bottomup(i + 1, w, items))
    }
  }
}
