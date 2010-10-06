import scala.collection.immutable.Set

object FromReport {

  def triPart_I(a: Set[Int], b1: Set[Int], b2: Set[Int], b3: Set[Int]) : Boolean = {
    require(
      (a == (b1 ++ b2 ++ b3)) &&
      (b1.max < b2.min) &&
      (b2.max < b3.min) &&
      (b1.size == b2.size) &&
      (b2.size == b3.size) &&
      (a.size == 12) &&
      (a.min == 1) 
    )
    (a.max != 12)
  } ensuring(_ == true)

  def binFind_V(left: Set[Int], right: Set[Int], v: Int, e: Int) : Boolean = {
    require(
      (left.max < v) &&
      (v < right.min) &&
      (e < v)
    )
      ((left ++ Set(v) ++ right).contains(e) == left.contains(e))
  } ensuring(_ == true)

  def pivot_V(oldAbove: Set[Int], pivot: Int, e: Int, newAbove: Set[Int]) : Boolean = {
    require(
      (oldAbove == Set.empty[Int] || pivot < oldAbove.min) &&
      (e > pivot) &&
      (newAbove == oldAbove ++ Set(e))
    )
    pivot < newAbove.min
  } ensuring(_ == true)

  def addSup_V(newSet: Set[Int], oldSet: Set[Int], large: Int) : Boolean = {
    require(
      (newSet == oldSet ++ Set(large)) &&
      (large >= oldSet.max)
    )
    newSet.max == large
  } ensuring(_ == true)
}
