package contracts


import org.scalacheck.{Arbitrary,Gen}
import org.scalacheck.Prop._
import org.scalacheck.ConsoleReporter.testStatsEx
import org.scalacheck.Test.check
import org.scalacheck.Arbitrary.arbitrary


import contracts.heap._

object LeftistHeapSpec {
  import contracts.heap.LeftistHeap._
  
  
  /**********************************************************/
  /*********************** GENERATORS ***********************/
  /**********************************************************/
  val genElem = for(v <- arbitrary[Int]) yield Elem(v)
  val genE = Gen.value(E)
  val genT = for {
    e <- arbitrary[Elem]
    h <- arbitrary[Heap]
  } yield h.insert(e)
  
  def genHeap: Gen[Heap] = Gen.lzy(Gen.oneOf(genE,genT))
   
  implicit def arbHeap: Arbitrary[Heap] = Arbitrary(genHeap)
  implicit def arbElem: Arbitrary[Elem] = Arbitrary(genElem)
  
  println(genHeap.sample)
  println(genHeap.sample)
  
  /**********************************************************/
  /*********************** PROPERTIES ***********************/
  /**********************************************************/
  val heapInsert = forAll( (heap: Heap, value: Elem) => content(heap.insert(value))(value) == content(heap)(value) + 1)
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
  def main(args: scala.Array[String]) = () 
   tests foreach { case (name, p) => testStatsEx(name, check(p))}
}
