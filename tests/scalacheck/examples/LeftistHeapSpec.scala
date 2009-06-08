package scalacheck.examples


import org.scalacheck.{Arbitrary,Properties,Gen}
import org.scalacheck.Prop._
import org.scalacheck.ConsoleReporter.testStatsEx
import org.scalacheck.Test.check
import org.scalacheck.Arbitrary.arbitrary


object LeftistHeapSpec {
  import contracts.heap._
  import contracts.heap.Heap._
  
  implicit def int2elem(x: Int): Elem = Elem(x)
  
  /**********************************************************/
  /*********************** GENERATORS ***********************/
  /**********************************************************/
  implicit def arbitraryHeap: Arbitrary[Heap] =
    Arbitrary(smallListInt.map(xs => {
      
      def makeHeap(h: Heap, xs: List[Int]): Heap = xs match {
        case Nil => h
        case x :: xs => makeHeap(h.insert(x),xs)
      }
                                             
      makeHeap(E, xs)
    }))
  
  // gen list (size undefined) of small integer (likely to have duplicates)
  val smallInt = Gen.choose(0,10) 
  val smallListInt = Gen.listOf[Int](smallInt)
  
  /**********************************************************/
  /*********************** PROPERTIES ***********************/
  /**********************************************************/
  val heapInsert = forAll( (heap: Heap, value: Int) => content(heap.insert(value))(value) == content(heap)(value) + 1)
  val heapFindMin = forAll{ heap : Heap => (heap.rankk > 0) ==> (heap.findMin == min(content(heap).elements.toList))}
  val heapDeleteMin = forAll{ heap: Heap => (heap.rankk > 0) ==> (content(heap.deleteMin).equals(content(heap) - heap.findMin))}
  val heapMerge = forAll( (thiz: Heap, that: Heap) => content(thiz.merge(that)).equals(content(thiz) +++ content(that)))
  
   /**********************************************************/
  // collect tests
  val tests = List(
    ("heapInsert",  heapInsert),
    ("heapFindMin", heapFindMin),
    ("heapDeleteMin", heapDeleteMin),
    ("heapMerge", heapMerge)
  )
  
  // main
  def main(args: scala.Array[String]) = 
    tests foreach { case (name, p) => testStatsEx(name, check(p)) }
}
