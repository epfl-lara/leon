import leon._
import mem._
import annotation._
import instrumentation._
//import leon.invariant._

object Knapscak {
  sealed abstract class IList {
    def size: BigInt = {
      this match {
        case Cons(_, tail) => 1 + tail.size
        case Nil() => BigInt(0)
      }
    } ensuring(_ >= 0)
  }
  case class Cons(x: (BigInt, BigInt), tail: IList) extends IList // a list of pairs of weights and values
  case class Nil() extends IList

  def deps(i: BigInt, items: IList): Boolean = {
    require(i >= 0)
    knapSack(i, items).isCached && // if we have the cached check only along the else branch, we would get a counter-example.
      (if (i <= 0) true
      else {
        deps(i - 1, items)
      })
  }

  @invstate
  def maxValue(items: IList, w: BigInt, currList: IList): BigInt = {
    require((w ==0 || (w > 0 && deps(w - 1, items))) &&
      // lemma inst
      (currList match {
        case Cons((wi, vi), _) =>
          if (wi <= w && wi > 0) depsLem(w - wi, w - 1, items)
          else true
        case Nil() => true
      }))
    currList match {
      case Cons((wi, vi), tail) =>
        val oldMax = maxValue(items, w, tail)
        if (wi <= w && wi > 0) {
          val choiceVal = vi + knapSack(w - wi, items)
          if (choiceVal >= oldMax)
            choiceVal
          else
            oldMax
        } else oldMax
      case Nil() => BigInt(0)
    }
  } ensuring(_ => time <= 40*currList.size + 20) // interchanging currList and items in the bound will produce a counter-example

  @memoize
  def knapSack(w: BigInt, items: IList): BigInt = {
    require(w >= 0 && (w == 0 || deps(w - 1, items)))
    if (w == 0) BigInt(0)
    else {
      maxValue(items, w, items)
    }
  } ensuring(_ => time <= 40*items.size + 25)

  def invoke(i: BigInt, items: IList) = {
    require(i == 0 || (i > 0 && deps(i - 1, items)))
    knapSack(i, items)
  } ensuring (res => {
    (i == 0 || depsMono(i - 1, items, inState[BigInt], outState[BigInt]) && // lemma inst
        deps(i - 1, items)) &&
      time <= 40*items.size + 40
  })

  def bottomup(i: BigInt, w: BigInt, items: IList): IList = {
    require(w >= i && (i == 0 || i > 0 && deps(i - 1, items)))
    val ri = invoke(i, items)
    if (i == w)
      Cons((i,ri), Nil())
    else {
      Cons((i,ri), bottomup(i + 1, w, items))
    }
  } ensuring(_ => items.size <= 10 ==> time <= 500 * (w - i + 1))

  /**
   * Computes the list of optimal solutions of all weights up to 'w'
   */
  def knapSackSol(w: BigInt, items: IList) = {
    require(w >= 0 && items.size <= 10) //  the second requirement is only to keep the bounds linear for z3 to work
    bottomup(0, w, items)
  } ensuring(_ => time <= 500*w + 510)

  /**
   * Lemmas of deps
   */
  // deps is monotonic
  @traceInduct
  def depsMono(i: BigInt, items: IList, st1: Set[Mem[BigInt]], st2: Set[Mem[BigInt]]) = {
    require(i >= 0)
    (st1.subsetOf(st2) && (deps(i, items) withState st1)) ==> (deps(i, items) withState st2)
  } holds

  // forall. x, x <= y && deps(y) => deps(x)
  @traceInduct
  def depsLem(x: BigInt, y: BigInt, items: IList) = {
    require(x >= 0 && y >= 0)
    (x <= y && deps(y, items)) ==> deps(x, items)
  } holds
}
