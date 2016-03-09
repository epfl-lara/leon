import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
//import leon.invariant._

object WeightedSched {
  sealed abstract class IList {
    def size: BigInt = {
      this match {
        case Cons(_, tail) => 1 + tail.size
        case Nil() => BigInt(0)
      }
    } ensuring(_ >= 0)
  }
  case class Cons(x: BigInt, tail: IList) extends IList
  case class Nil() extends IList

  /**
   * array of jobs
   * (a) each job has a start time, finish time, and weight
   * (b) Jobs are sorted in ascending order of finish times
   */
  @ignore
  var jobs = Array[(BigInt, BigInt, BigInt)]()

  /**
   * A precomputed mapping from each job i to the previous job j it is compatible with.
   */
  @ignore
  var p = Array[Int]()

  @extern
  def jobInfo(i: BigInt) = {
    jobs(i.toInt)
  } ensuring(_ => time <= 1)

  @extern
  def prevCompatibleJob(i: BigInt) = {
    BigInt(p(i.toInt))
  } ensuring(res => res >=0 && res < i && time <= 1)

  @inline
  def max(x: BigInt, y: BigInt) = if (x >= y) x else y

  def depsEval(i: BigInt) = i == 0 || (i > 0 && allEval(i-1))

  def allEval(i: BigInt): Boolean = {
    require(i >= 0)
    sched(i).isCached &&
      (if (i == 0) true
      else allEval(i - 1))
  }

  @traceInduct
  def evalMono(i: BigInt, st1: Set[Mem[BigInt]], st2: Set[Mem[BigInt]]) = {
    require(i >= 0)
    (st1.subsetOf(st2) && (allEval(i) withState st1)) ==> (allEval(i) withState st2)
  } holds

  @traceInduct
   def evalLem(x: BigInt, y: BigInt) = {
    require(x >= 0 && y >= 0)
    (x <= y && allEval(y)) ==> allEval(x)
  } holds

  @invstate
  @memoize
  def sched(jobIndex: BigInt): BigInt = {
    require(depsEval(jobIndex) &&
        (jobIndex == 0 || evalLem(prevCompatibleJob(jobIndex), jobIndex-1)))
    val (st, fn, w) = jobInfo(jobIndex)
    if(jobIndex == 0) w
    else {
      // we may either include the head job or not:
      // if we include the head job, we have to skip every job that overlaps with it
      val tailValue = sched(jobIndex - 1)
      val prevCompatVal = sched(prevCompatibleJob(jobIndex))
      max(w + prevCompatVal, tailValue)
    }
  } ensuring(_ => time <= 100)

  def invoke(jobIndex: BigInt) = {
    require(depsEval(jobIndex))
    sched(jobIndex)
  } ensuring (res => {
    val in = inState[BigInt]
    val out = outState[BigInt]
    (jobIndex == 0 || evalMono(jobIndex-1, in, out)) &&
      time <= 150
  })

  def schedBU(jobi: BigInt): IList = {
    require(jobi >= 0)
    if(jobi == 0) {
        Cons(invoke(jobi), Nil())
    } else {
      val tailRes =  schedBU(jobi-1)
      Cons(invoke(jobi), tailRes)
    }
  } ensuring(_ => allEval(jobi) &&
		  	time <= 200 * (jobi + 1))
}
