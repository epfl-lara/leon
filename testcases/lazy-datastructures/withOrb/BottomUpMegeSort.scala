package withOrb

import leon._
import lazyeval._
import lang._
import annotation._
import instrumentation._
import invariant._
import stats._

/**
 * TODO Multiple instantiations of type parameters is not supported yet,
 * since it require creation of multiple states one for each instantiation
 */

/**
 * A version of merge sort that operates bottom-up. That allows
 * accessing the first element in the sorted list in constant time.
 */
object BottomUpMergeSort {

  /**
   * A list of integers that have to be sorted
   */
  sealed abstract class IList {
    def size: BigInt = {
      this match {
        case ICons(_, xs) => 1 + xs.size
        case _            => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  case class ICons(x: BigInt, tail: IList) extends IList
  case class INil() extends IList

  /**
   * A stream of integers (the tail is lazy)
   */
  sealed abstract class IStream {
    def size: BigInt = {
      this match {
        case SCons(_, xs) => 1 + ssize(xs)
        case _            => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  case class SCons(x: BigInt, tail: Lazy[IStream]) extends IStream
  case class SNil() extends IStream
  @inline
  def ssize(l: Lazy[IStream]): BigInt = (l*).size

  /**
   * A list of suspensions
   */
  sealed abstract class LList {
    def size: BigInt = {
      this match {
        case LNil()      => BigInt(0)
        case LCons(_, t) => 1 + t.size
      }
    } ensuring (_ >= 0)

    def valid: Boolean = {
      this match {
        case LNil()      => true
        case LCons(l, t) => ssize(l) > 0 && t.valid
      }
    }

    def fullSize: BigInt = {
      this match {
        case LNil()      => BigInt(0)
        case LCons(l, t) => ssize(l) + t.fullSize
      }
    } ensuring (_ >= 0)
  }
  case class LCons(x: Lazy[IStream], tail: LList) extends LList
  case class LNil() extends LList

  /**
   * A function that given a list of (lazy) sorted lists,
   * groups them into pairs and lazily invokes the 'merge' function
   * on each pair.
   * Takes time linear in the size of the input list
   */
  @invisibleBody
  def pairs(l: LList): LList = {
    require(l.valid)
    l match {
      case LNil()           => LNil()
      case LCons(_, LNil()) => l
      case LCons(l1, LCons(l2, rest)) =>
        LCons($(merge(l1, l2)), pairs(rest))
    }
  } ensuring (res => res.size <= (l.size + 1) / 2 &&
    l.fullSize == res.fullSize &&
    res.valid &&
    time <= ? * l.size + ?)

  /**
   * Create a linearized tree of merges e.g. merge(merge(2, 1), merge(17, 19)).
   * Takes time linear in the size of the input list.
   */
  @invisibleBody
  def constructMergeTree(l: LList): LList = {
    require(l.valid)
    l match {
      case LNil()           => LNil()
      case LCons(_, LNil()) => l
      case _ =>
        constructMergeTree(pairs(l))
    }
  } ensuring {res =>
    res.size <= 1 && res.fullSize == l.fullSize &&
    (res match {
      case LCons(il, LNil()) =>
        res.fullSize == ssize(il) // this is implied by the previous conditions
      case _ => true
    }) &&
    res.valid &&
    time <= ? * l.size + ?}

  /**
   *  A function that merges two sorted streams of integers.
   *  Note: the sorted stream of integers may by recursively constructed using merge.
   *  Takes time linear in the size of the streams (non-trivial to prove due to cascading of lazy calls)
   */
  @invisibleBody
  @usePost
  def merge(a: Lazy[IStream], b: Lazy[IStream]): IStream = {
    require(((a*) != SNil() || b.isEvaluated) && // if one of the arguments is Nil then the other is evaluated
        ((b*) != SNil() || a.isEvaluated) &&
        ((a*) != SNil() || (b*) != SNil())) // at least one of the arguments is not Nil
    b.value match {
      case SNil() => a.value
      case bl @ SCons(x, xs) =>
        a.value match {
          case SNil() => bl
          case SCons(y, ys) =>
            if (y < x)
              SCons(y, $(merge(ys, b)))
            else
              SCons(x, $(merge(a, xs)))
        }
    }
  } ensuring (res => ssize(a) + ssize(b) == res.size &&
       //time <= ? * res.size + ?) // note: res.size >= 1 // here stack is max of a and b
      time <= 67 * res.size - 47) // Orb cannot infer this due to issues with CVC4 set solving !

  /**
   * Converts a list of integers to a list of streams of integers
   */
  val nilStream: IStream = SNil()

  @invisibleBody
  def IListToLList(l: IList): LList = {
    l match {
      case INil() => LNil()
      case ICons(x, xs) =>
        LCons(SCons(x, nilStream), IListToLList(xs))
    }
  } ensuring { res =>
    res.fullSize == l.size &&
      res.size == l.size &&
      res.valid &&
      time <= ? * l.size + ?
  }

  /**
   * Takes list of integers and returns a sorted stream of integers.
   * Takes time linear in the size of the  input since it sorts lazily.
   */
  def mergeSort(l: IList): IStream = {
    l match {
      case INil() => SNil()
      case _ =>
        constructMergeTree(IListToLList(l)) match {
          case LCons(r, LNil()) => r.value
        }
    }
  } ensuring (res => time <= ? * l.size + ?)

  /**
   * A function that accesses the first element of a list using lazy sorting.
   */
  def firstMin(l: IList) : BigInt ={
    require(l != INil())
    mergeSort(l) match {
      case SCons(x, rest) => x
    }
  } ensuring (res => time <= ? * l.size + ?)

  def kthMin(l: IStream, k: BigInt): BigInt = {
    require(k >= 0)
    l match {
      case SCons(x, xs) =>
        if (k == 0) x
        else
          kthMin(xs.value, k - 1)
      case SNil() => BigInt(0)
    }
  } //ensuring (_ => time <= ? * (k * ssize(l)) + ? * k + ?)

  @ignore
  def main(args: Array[String]) {
    //import eagerEval.MergeSort
    import scala.util.Random
    import scala.math.BigInt
    import stats._
    import collection._

    println("Running merge sort test...")
    val length = 3000000
    val maxIndexValue = 100
    val randomList = Random.shuffle((0 until length).toList)
    val l1 = randomList.foldRight(List[BigInt]()){
      case (i, acc) => BigInt(i) :: acc
    }
    val l2 = randomList.foldRight(INil(): IList){
      case (i, acc) => ICons(BigInt(i), acc)
    }
    println(s"Created inputs of size (${l1.size},${l2.size}), starting operations...")
    val sort2 = timed{ mergeSort(l2) }{t => println(s"Lazy merge sort completed in ${t/1000.0} sec") }
    //val sort1 = timed{ MergeSort.msort((x: BigInt, y: BigInt) => x <= y)(l1) } {t => println(s"Eager merge sort completed in ${t/1000.0} sec") }
    // sample 10 elements from a space of [0-100]
    val rand = Random
    var totalTime1 = 0L
    var totalTime2 = 0L
    for(i <- 0 until 10) {
      val idx = rand.nextInt(maxIndexValue)
      //val e1 = timed { sort1(idx) } { totalTime1 +=_ }
      val e2 = timed { kthMin(sort2, idx) }{ totalTime2 += _ }
      //println(s"Element at index $idx - Eager: $e1 Lazy: $e2")
      //assert(e1 == e2)
    }
    println(s"Time-taken to pick first 10 minimum elements - Eager: ${totalTime1/1000.0}s Lazy: ${totalTime2/1000.0}s")
  }
}
