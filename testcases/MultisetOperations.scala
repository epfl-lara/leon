import scala.collection.immutable.Set
import scala.collection.immutable.Multiset

object MultisetOperations {
  def preservedUnderToSet(a: Multiset[Int], b: Multiset[Int]) : Boolean = {
    ((a ++ b).toSet.size == (a.toSet ++ b.toSet).size) &&
    ((a ** b).toSet.size == (a.toSet ** b.toSet).size)
  } ensuring(res => res)

  def sumPreservesSizes(a: Multiset[Int], b: Multiset[Int]) : Boolean = {
    ((a +++ b).size == a.size + b.size)
  } ensuring(res => res)
}
