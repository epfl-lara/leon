package withOrb

import leon._
import lang._
import annotation._
import instrumentation._
import invariant._
import leon.collection._
import mem._
import higherorder._
import stats._

/**
 * A version of merge sort that operates bottom-up. That allows
 * accessing the first element in the sorted list in constant time.
 */
object BottomUpMergeSort {
  sealed abstract class LList {
    def size: BigInt = {
      this match {
        case SCons(_, t) => 1 + t.size
        case _            => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  case class SCons(x: BigInt, tailFun: Stream) extends LList
  case class SNil() extends LList
  case class Stream(lfun: () => LList) {
    @inline
    def size = (list*).size
    lazy val list: LList = lfun()    
  }
 
  def valid(sl: List[Stream]): Boolean = {
    sl match {
      case Cons(s, tail) => s.size > 0  && valid(tail)
      case Nil() => true
    }
  }

  def fullSize(sl: List[Stream]): BigInt = {
    sl match {
      case Nil()      => BigInt(0)
      case Cons(l, t) => l.size + fullSize(t)
    }
  } ensuring (_ >= 0)

  /**
   * A function that given a list of (lazy) sorted lists,
   * groups them into pairs and lazily invokes the 'merge' function on each pair.
   * Takes time linear in the size of the input list.
   */
  @invisibleBody
  def pairs(l: List[Stream]): List[Stream] = {
    require(valid(l))
    l match {
      case Nil()           => Nil[Stream]()
      case Cons(_, Nil()) => l
      case Cons(l1, Cons(l2, rest)) =>
        Cons(Stream(() => merge(l1, l2)), pairs(rest))
    }
  } ensuring (res => res.size <= (l.size + 1) / 2 &&
    fullSize(l) == fullSize(res) &&
    valid(res) && 
    time <= ? * l.size + ?
    )

  /**
   * Create a linearized tree of merges e.g. merge(merge(2, 1), merge(17, 19)).
   * Takes time linear in the size of the input list.
   */
  @invisibleBody
  def constructMergeTree(l: List[Stream]): List[Stream] = {
    require(valid(l))
    l match {
      case Nil()           => Nil[Stream]()
      case Cons(_, Nil()) => l
      case _ =>
        constructMergeTree(pairs(l))
    }
  } ensuring {res =>
    res.size <= 1 && fullSize(res) == fullSize(l) &&
    (res match {
      case Cons(il, Nil()) =>
        fullSize(res) == il.size // this is implied by the previous conditions
      case _ => true
    }) &&
    valid(res) && 
    time <= ? * l.size + ?
  }

  /**
   *  A function that merges two sorted streams of integers.
   *  Note: the sorted stream of integers may by recursively constructed using merge.
   *  Takes time linear in the size of the streams (non-trivial to prove due to cascading of lazy calls)
   */
  @invisibleBody
  @usePost
  def merge(a: Stream, b: Stream): LList = {
    require(((a.list*) != SNil() || b.list.cached) && // if one of the arguments is Nil then the other is evaluated
        ((b.list*) != SNil() || a.list.cached) &&
        ((a.list*) != SNil() || (b.list*) != SNil())) // at least one of the arguments is not Nil
    b.list match {
      case SNil() => a.list
      case bl @ SCons(x, xs) =>
        a.list match {
          case SNil() => bl
          case SCons(y, ys) =>
            if (y < x)
              SCons(y, Stream(() => merge(ys, b)))
            else
              SCons(x, Stream(() => merge(a, xs)))
        }
    }
  } ensuring (res => a.size + b.size == res.size &&
       time <= ? * res.size + ?) // note: res.size >= 1 // here stack is max of a and b
     // time <= 67 * res.size - 47) // Orb cannot infer this due to issues with CVC4 set solving !

  /**
   * Converts a list of integers to a list of streams of integers
   */
  @inline
  val nilStream: Stream = Stream(lift(SNil()))

  @invisibleBody
  def ListToStreamList(l: List[BigInt]): List[Stream] = {
    l match {
      case Nil() => Nil[Stream]()
      case Cons(x, xs) =>
        Cons[Stream](Stream(lift(SCons(x, nilStream))), ListToStreamList(xs))
    }
  } ensuring { res =>
    fullSize(res) == l.size &&
      res.size == l.size &&
      valid(res) && 
      time <= ? * l.size + ?
  }

  /**
   * Takes list of integers and returns a sorted stream of integers.
   * Takes time linear in the size of the  input since it sorts lazily.
   */
  def mergeSort(l: List[BigInt]): LList = {
    l match {
      case Nil() => SNil()
      case _ =>
        constructMergeTree(ListToStreamList(l)) match {
          case Cons(r, Nil()) => r.list
        }
    }
  } ensuring (res => time <= ? * l.size + ?)

  /**
   * A function that accesses the first element of a list using lazy sorting.
   */
//  def firstMin(l: IList) : BigInt ={
//    require(l != INil())
//    mergeSort(l) match {
//      case SCons(x, rest) => x
//    }
//  } ensuring (res => time <= ? * l.size + ?)
//
//  def kthMin(l: IStream, k: BigInt): BigInt = {
//    require(k >= 0)
//    l match {
//      case SCons(x, xs) =>
//        if (k == 0) x
//        else
//          kthMin(xs.value, k - 1)
//      case SNil() => BigInt(0)
//    }
//  } //ensuring (_ => time <= ? * (k * ssize(l)) + ? * k + ?)

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
    val l2 = randomList.foldRight(Nil[BigInt](): List[BigInt]){
      case (i, acc) => Cons(BigInt(i), acc)
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
      //val e2 = timed { kthMin(sort2, idx) }{ totalTime2 += _ }
      //println(s"Element at index $idx - Eager: $e1 Lazy: $e2")
      //assert(e1 == e2)
    }
    println(s"Time-taken to pick first 10 minimum elements - Eager: ${totalTime1/1000.0}s Lazy: ${totalTime2/1000.0}s")
  }
}
