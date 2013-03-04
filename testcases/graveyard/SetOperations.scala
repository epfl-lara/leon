import scala.collection.immutable.Set

// Cardinalities not supported yet.
// Pre/Post conditions commented out.

object SetOperations {
  
  /* Sets of type Set[Int] */

  def wrongAdd(a : Set[Int], b: Int) : Set[Int] = {
    a ++ Set(b)
  } ensuring (_ == a)

  // Pure BAPA verification condition
  def vennRegions(a: Set[Int], b: Set[Int], c: Set[Int]) = {
    a ++ b ++ c
  } ensuring {
    _.size ==
            a.size + b.size + c.size -
            (a ** b).size - (b ** c).size - (c ** a).size +
            (a ** b ** c).size
  }
  
  // Ordered BAPA verification condition
  def add(a: Set[Int], b: Int): Set[Int] = {
    require(a.size >= 0)
    a ++ Set(b)
  } ensuring ((x: Set[Int]) => x.size >= a.size)

  /* Sets of type Set[Set[Int]] */
  
  // This still works ..
  def vennRegions2(a: Set[Set[Int]], b: Set[Set[Int]], c: Set[Set[Int]]) = {
    a ++ b ++ c
  } ensuring {
    _.size ==
            a.size + b.size + c.size -
            (a ** b).size - (b ** c).size - (c ** a).size +
            (a ** b ** c).size
  }
  
  // OrderedBAPA verification with Min and Max
  def expandSet(a: Set[Int]) : Set[Int] = {
    require(a.size >= 1)
    val x = a.min - 1
    val y = a.max + 1
    Set(x) ++ Set(y) ++ a
  } ensuring (res => res.max > a.max && res.min < a.min)

  // .. but this can no longer be proved by the OrderedBAPA solver,
  // because "Set(b)" is neither a set of uninterpreted elements (pure BAPA)
  // nor it is a set of integers (ordered BAPA).
  //
  // Perhaps "Set(b)" can be approximated by a fresh set variable S,
  // with |S| = 1 ? More general, we can approximate "FiniteSet(elems)"
  // by a fresh set variable S with |S| <= [# of elems].
  // (Though, there is a problem with min/max expressions appearing recursively
  //  in the FiniteSet.) 
  def add2(a: Set[Set[Int]], b: Set[Int]): Set[Set[Int]] = {
    require(a.size >= 0)
    a ++ Set(b)
  } ensuring ((x: Set[Set[Int]]) => x.size >= a.size)
  
}
