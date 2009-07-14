package scalatest.examples

import org.scalatest.matchers.ShouldMatchers
import org.scalatest.Spec

import contracts.heap._

/**
 * Test description of the behavior expected by a leftist heap. 
 */
class LeftistHeapSpec extends Spec with ShouldMatchers {

  implicit def int2elem(x: Int): Elem = Elem(x)
  
  describe("A Leftis Heap") {
    it("should insert elements in the heap and keep the heap ordered")  {
      val heap = T(1,Elem(1),E,E)
      
      (heap.insert(-1)) should equal (T(1,Elem(-1),T(1,Elem(1),E,E),E))
      (heap.insert(1)) should equal (T(1,Elem(1),T(1,Elem(1),E,E),E))
      
    }
    
  }
}
