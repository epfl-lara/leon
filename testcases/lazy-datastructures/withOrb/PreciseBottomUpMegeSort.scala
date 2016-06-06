//package withOrb

import leon._
import lang._
import annotation._
import instrumentation._
import invariant._
import mem._
import higherorder._
import stats._

/**
 * Computing the kthe min using a version of merge sort that operates bottom-up.
 * This allows accessing the first element in the sorted list in O(n) time,
 * and kth element in O(kn) time.
 * Needs unrollfactor = 3
 */
object BottomUpMergeSortPrecise {  
  
  @inline
  def max(x:BigInt, y:BigInt) = if (x >= y) x else y   
  
  sealed abstract class List[T] {  
    def size: BigInt = (this match {
      case Nil() => BigInt(0)
      case Cons(h, t) => 1 + t.size
    }) ensuring (_ >= 0)
    
    // length is used in the implementation
    val length: BigInt = (this match {
      case Nil() => BigInt(0)
      case Cons(h, t) => 1 + t.length
    }) ensuring (_ == size)
  }
  case class Cons[T](x: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]
  
  private sealed abstract class LList {
    def size: BigInt = {
      this match {
        case SCons(_, t) => 1 + t.size
        case _            => BigInt(0)
      }
    } ensuring (_ >= 0)
    
    def height: BigInt = {     
      this match {
        case SCons(_, t) => t.height
        case _            => BigInt(0)
      }          
    } ensuring(_ >= 0)

    def weightBalanced: Boolean = {
      this match {
        case SCons(_, t) => t.weightBalanced
        case _            => true
      }
    }
  }
  private case class SCons(x: BigInt, tailFun: Stream) extends LList
  private case class SNil() extends LList
  private case class Stream(lfun: () => LList) {
    @inline
    def size = (list*).size
    lazy val list: LList = lfun()
        
    def height: BigInt = {
      (lfun fmatch[LList, Stream, BigInt] {
        case (a, b) if lfun.is(() => mergeSusp(a, b)) => 1 + max(a.height, b.height)
        case _ => BigInt(0)
      }): BigInt  
    }ensuring(_ >= 0)

    //@invisibleBody
    def weightBalanced: Boolean = {
      lfun fmatch[LList, Stream, Boolean] {
        case (a, b) if lfun.is(() => mergeSusp(a, b)) =>
          val sizeDiff = a.size - b.size
          sizeDiff >= -2 && sizeDiff <= 2 && 
          a.weightBalanced && b.weightBalanced
        case _ => true 
      }
    }
  }
  
  @inline
  private val nilStream: Stream = Stream(() => SNil())
  
  @monotonic
  def log(x: BigInt) : BigInt = {
    require(x >= 0)
    if(x <= 1) BigInt(0)
    else
      1 + log(x/2)
  } ensuring(_ >= 0)
  
  //@inline
  def recSizeL(l: LList): BigInt = {
    require(l != SNil())
    l match {  
      //case SNil() => BigInt(0)
      case SCons(_, t) => 1 + recSize(t)
    }
  }
  
  def recSize(l: Stream): BigInt = {
    require(l.weightBalanced)
    (l.lfun fmatch[LList, Stream, BigInt] {
      case (a, b) if l.lfun.is(() => mergeSusp(a, b)) => recSizeL(a) + recSize(b)
      case _ => BigInt(0)
    }) : BigInt         
  } ensuring (res => l.size == res && 
      l.height <= ? * log(res) + ?)

  /**
   * 
   * this method is a functional implementation of buildheap in linear time.
   */
  @invisibleBody
  private def constructMergeTree(l: List[BigInt], from: BigInt, to: BigInt): (LList, List[BigInt]) = { 
    require(from <= to && from >= 0 && (to - from + 1) <= l.size )        
    l match {
      case Nil()           => (SNil(), Nil[BigInt]()) // this case is unreachable
      case Cons(x, tail)  => 
        if(from == to) (SCons(x, nilStream), tail)
        else {
          val mid = (from + to) / 2
          val (lside, midlist) = constructMergeTree(l, from, mid)
          val (rside, rest) = constructMergeTree(midlist, mid + 1, to)
          (merge(lside, rside), rest)
        }
    }
  } ensuring{ res =>    
    val range = to - from + 1
    val (reslist, rest) = res
    reslist.size == range && 
    rest.size == l.size - range  &&
    reslist.weightBalanced //&& 
    //reslist.valid &&
    //time <= ? * range + ? // 57 * range - 44 TODO: check why making this - fails a requirement
  }

  @invisibleBody
  private def merge(a: LList, b: LList): LList = {
    b match {
      case SNil() => a
      case SCons(x, xs) =>
        a match {
          case SNil() => b
          case SCons(y, ys) =>
            if (y < x)
              SCons(y, Stream(() => mergeSusp(b, ys))) // here, the order of arguments is changed, the sort is not a stable sort
            else
              SCons(x, Stream(() => mergeSusp(a, xs)))
        }
    }
  } ensuring{res => a.size + b.size == res.size //&& 
    //time <= ? // time <= 16
  }

  /**
   *  A function that merges two sorted streams of integers.
   *  Note: the sorted stream of integers may by recursively constructed using merge.
   *  Takes time linear in the size of the streams (non-trivial to prove due to cascading of lazy calls)
   */
  @invisibleBody
  private def mergeSusp(a: LList, b: Stream): LList = {
    require(a != SNil()) // && a.valid && b.valid)
    merge(a, b.list)
  } ensuring {res =>        
    res != SNil() &&
    res.height <= max(a.height, b.height) + 1 //&&
    //time <= ? * b.height + ? // 22 * b.height + 1    
  }  
  
  /**
   * Takes list of integers and returns a sorted stream of integers.
   * Takes time linear in the size of the  input since it sorts lazily.
   */  
  @invisibleBody
  private def mergeSort(l: List[BigInt]): LList = {
    l match {
      case Nil() => SNil()
      case _ => constructMergeTree(l, 0, l.length - 1)._1 
    }
  } ensuring (res => l.size == res.size )// && time <= ? * l.size + ?) // 57 * l.size + 3
  
  private def kthMinRec(l: LList, k: BigInt): BigInt = {
    require(k >= 0) // && l.valid)
    l match {
      case SCons(x, xs) =>
        if (k == 0) x
        else
          kthMinRec(xs.list, k - 1)
      case SNil() => BigInt(0)
    }
  } //ensuring (_ => time <= ? * (k * l.height) + ?) //  time <= 22 * (k * l.height) + 6
  //TODO Add the ? * (l.height) term if the numbers do not match the runtime estimate 
  /**
   * A function that accesses the kth element of a list using lazy sorting.
   */
//  def kthMin(l: List[BigInt], k: BigInt): BigInt = {
//    kthMinStream(mergeSort(l), k)
//  } ensuring(_ => time <= ? * (k * l.size) + ? * (l.size) + ?)

  @ignore
  def main(args: Array[String]) {
    //import eagerEval.MergeSort
    import scala.util.Random
    import scala.math.BigInt
    import stats._    

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
