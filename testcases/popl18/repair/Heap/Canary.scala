import leon.lang._
import leon.collection._
import Heaps._

// Canary file for statistics extractor which lists the types in which we are interested

object Canary {
  def dummy[A]: A = error[A]("no impl.")

  def canary_BigInt: BigInt = dummy

  def canary_BigInt_List: List[BigInt] = dummy

  def canary_BigInt_Set: Set[BigInt] = dummy

  def canary_BigInt_Option: Option[BigInt] = dummy

  def canary_Heap: Heap = dummy

}
