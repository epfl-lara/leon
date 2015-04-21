import leon.annotation._
import leon.lang._

/** Examples of iteration over set elements using 'epsilon'.
 *
 * First we implement a test for containment. This can easily be verified
 * correct by Leon — because the post-condition can be specified concisely in
 * concepts Leon understands.
 * 
 * Next we implement a test for wether all values are at least some minimum,
 * and try to prove that (∀x. x≥5) → (∀x. x≥2). Leon fails to prove this,
 * despite proving an equivalent formulation using linked lists instead of sets
 * (SimpleInduction.scala).
 * 
 * Finally, we implement a method to find the cardinality of a set. Leon can
 * prove things with this on concrete sets, as seen in sizeTest1(), but not on
 * arbitrary sets, as in sizeTest2().
 */
object SetIteration {
  def iterateContains(set: Set[Int], v : Int) : Boolean ={
    if (set == Set.empty[Int])
      false
    else {
      val elt = epsilon( (i : Int) => set.contains(i) )
      if (elt==v)
        true
      else
        iterateContains(set -- Set(elt), v)
    }
  } ensuring (_ == set.contains(v))
  
  def contTest(set : Set[Int], v : Int) : Boolean = {
    set.contains(v) == iterateContains(set, v)
  } holds
  
  
  def iterateMinVal(set: Set[Int], v : Int) : Boolean ={
    if (set == Set.empty[Int])
      true
    else {
      val elt = epsilon( (i : Int) => set.contains(i) )
      if (elt >= v)
        iterateMinVal(set -- Set(elt), v)
      else
        false
    }
  }
  
  def sizeMinVal(set : Set[Int]) : Boolean = {
    !iterateMinVal(set, 5) || iterateMinVal(set, 2)
  } holds       // proof fails
  
  
  def iterateSize(set: Set[Int]) : Int ={
    if (set == Set.empty[Int])
      0
    else {
      val elt = epsilon( (i : Int) => set.contains(i) )
      1 + iterateSize(set -- Set(elt))
    }
  }ensuring (_ >= 0)
  
  def sizeTest1() : Boolean = {
    iterateSize(Set.empty)+3 == iterateSize(Set(4,8,22))
  } holds
  def sizeTestFalse(set : Set[Int]) : Boolean = {
    val size1 = iterateSize(set)
    val size2 = iterateSize(set ++ Set(32))
    size1+1 == size2
  } holds       // gives correct counter example: set=Set(32)
  def sizeTest2(set : Set[Int]) : Boolean = {
    val size1 = iterateSize(set)
    val size2 = iterateSize(set ++ Set(32))
    size1+1 == size2 || size1 == size2
  } holds       // proof fails
}
