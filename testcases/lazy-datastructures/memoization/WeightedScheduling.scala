import leon.lazyeval._
import leon.lazyeval.Mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
//import leon.invariant._

object WeightedSched {
  /*sealed abstract class IList {
    def size: BigInt = {
      this match {
        case Cons(_, tail) => 1 + tail.size
        case Nil() => BigInt(0)
      }
    } ensuring(_ >= 0)
  }
  case class Cons(x: (BigInt, BigInt, BigInt), tail: IList) extends IList // a list of pairs of start, finish and weights
  case class Nil() extends IList

  sealed abstract class LList {
    def size: BigInt = {
      this match {
        case LCons(_, _, tail) => 1 + tail.size
        case LNil() => BigInt(0)
      }
    } ensuring(_ >= 0)
  }
  case class LCons(l: IList, pl: LList, tail: LList) extends LList // a list of pointers into IList, and LList
  case class LNil() extends LList*/

  def lookupP(i: BigInt): BigInt = {

  }

  def jobs(i: BigInt): BigInt = {

  }

  @inline
  def max(x: BigInt, y: BigInt) = if (x >= y) x else y

  def allEval(jobs: IList): Boolean = {
    optValOfSched(jobs).isCached &&
      (jobs match {
        case Nil()         => true
        case Cons(_, tail) => allEval(tail)
      })
  }

  def depsEval(jobs: IList): Boolean = {
    jobs match {
      case Nil() => true
      case Cons(_, tail) => allEval(tail)
    }
  }

  @traceInduct
  def evalMono(jobs: IList, st1: Set[Mem[BigInt]], st2: Set[Mem[BigInt]]) = {
    (st1.subsetOf(st2) && (allEval(jobs) withState st1)) ==> (allEval(jobs) withState st2)
  } holds

  @invstate
  def skip(jobs: IList, finishBound: BigInt): BigInt = {
    require(allEval(jobs))
    jobs match {
      case Nil() => BigInt(0)
      case Cons((st, fn, v), tail) =>
        if(fn > finishBound)
          skip(tail, finishBound) // cannot include this
          else
            optValOfSched(jobs)
    }
  } //ensuring(_ => time <= 40*currList.size + 20) // interchanging currList and items in the bound will produce a counter-example

  /**
   * (a) assuming that jobs are sorted in descending order of the finish times
   * (b) 'prev' - previous compatibility list for each job (assuming it is precomputed)
   */
  @memoize
  def optValOfSched(jobs: IList, prev: LList): BigInt = {
    //require(depsEval(jobs))
    (jobs, prev) match {
      case (Nil(), _) => BigInt(0)
      case (Cons((st, fn, v), tail), LCons(prevJobs, prevPres, ptail)) =>
        val tailres = optValOfSched(tail, ptail)
        // we may either include the head job or not:
        // if we include the head job, we have to skip every job that overlaps with it
        max(v + optValOfSched(prevJobs, prevPres), tailres)
      case _ =>
        BigInt(0) // these cases should not be reachable
    }
  } ensuring(res => {
    val in = Mem.inState[BigInt]
    val out = Mem.outState[BigInt]
    ((depsEval(jobs) withState in) ==> (in == out)) &&
      depsEval(jobs) &&
      (jobs match {
        case Nil() => true
        case Cons(_, tail) =>
          evalMono(tail, out, out ++ Set(Mem(optValOfSched(jobs)))) // lemma instantiation
      })
  })

  /*def invoke(jobs: IList) = {
    require(depsEval(jobs))
    optValOfSched(jobs)
  } ensuring (res => {
    val in = $.inState[BigInt]
    val out = $.outState[BigInt]
    (jobs match {
      case Nil() => true
      case Cons(_, tail) => evalMono(tail, in, out)
    }) &&
    allEval(jobs) //&&
      //time <= 40*items.size + 40
  })*/

  /*def bottomup(jobs: IList): IList = {
    jobs match {
      case Nil() =>
        Cons((0, 0, invoke(jobs)), Nil())
      case Cons((st, ft, value), tail) =>
        val tailres = bottomup(tail)
        Cons((st, ft, invoke(jobs)), tailres)
    }
  } ensuring(_ => allEval(jobs))*/
    //items.size <= 10 ==> time <= 500 * (w - i + 1))

  /**
   * Given a list of jobs (with weights) sorted in descending order of their finish times,
   * computes the value of the optimal scheduling scheduling.
   */
  /*def optSols(jobs: IList) = {
    //require(w >= 0 && items.size <= 10) //  the second requirement is only to keep the bounds linear for z3 to work
    bottomup(jobs)
  } //ensuring(time <= 500*w + 510)
*/
}
