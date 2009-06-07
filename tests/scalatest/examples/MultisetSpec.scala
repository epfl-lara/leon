package scalatest.examples

import org.scalatest.matchers.ShouldMatchers
import org.scalatest.Spec

import scala.collection.immutable.HashMultiset

/**
 * Test description of the behavior expected by a multiset. 
 */
class MultisetSpec extends Spec with ShouldMatchers  {

  describe("A Multiset") {
    
    it("should have no element if empty.") {
      val empty = HashMultiset.empty[Int]
      
      empty should have size 0
      empty should be ('empty)
      assert(!empty.elements.hasNext)
      empty(0) should be (0)
      empty should not contain (0)
    }
    
    it("should increase the cardinality of identical elements.") {
      val mset = HashMultiset(1,1,2)
      
      mset should not be ('empty)
      mset should have size 3
      mset(1) should be (2)
      mset(2) should be (1)
      mset(3) should be (0)
    }
    
    it("should implement structural equality when comparing two multisets.") {
      val empty1 = HashMultiset.empty[Int]
      val empty2 = HashMultiset.empty[Int]
      
      val filled1 = HashMultiset(1,1,2)
      val filled2 = HashMultiset.empty[Int] + (1,1,2)
      
      empty1 should equal (empty2)
      filled1 should equal (filled2)
      
      filled1 should not equal (empty1)
    }
    
    it("should held be empty if intersected with an empty multiset.") {
      val mset = HashMultiset(1,1,2)
      val empty = HashMultiset.empty[Int]
      
      //check that "**" and "intersect" are indeed alias one of the other 
      (empty ** empty) should equal (empty)
      (empty intersect empty) should equal (empty)
      
      (empty ** mset) should equal (empty)
      (empty intersect mset) should equal (empty)
      
      (mset ** empty) should equal (empty)
      (mset intersect empty) should equal (empty)
    }
    
    it("should not change when interseced/unified with itself.") {
      val mset = HashMultiset(1,1,2,0,3)
      
      (mset ** mset) should equal (mset)
      (mset ++ mset) should equal (mset)
    }
    
    it("should decrease the cardinality of an element when removed.") {
      val mset = HashMultiset(1,2,1)
      
      (mset -- List(1)) should equal (HashMultiset(1,2))
      (mset -- List(1)) should equal (HashMultiset(2,1))
      (mset -- List(1,2)) should equal (HashMultiset(1))
      (mset -- List(1,1,2)) should be ('empty)
      
      ((mset -- List(1)).apply(1)) should be (1)
      ((mset -- List(1)).apply(2)) should be (1)
      ((mset -- List(2)).apply(1)) should be (2)
      (mset -- List(1,1,2)) should not contain (0)
    }
    
    it("should never contains an element with cardinality lower than zero.") {
      val mset = HashMultiset(1)
      
      (mset -- List(1)) should be ('empty)
      (mset -- List(1,1)) should be ('empty)
      (mset -- List(1,1)) should not contain (0)
      
      ((mset -- List(1,1)) ++ List(1)) should contain (1)
    }
    
    it("can be degenerated to a set.") {
      val mset = HashMultiset(1,1,1,1,1,1,2,2,2,2,2,3,4)
      val set = mset.asSet
      
      set should have size (4) 
      List(1,2,3,4).forall(set.contains(_))
    }
  }
}
