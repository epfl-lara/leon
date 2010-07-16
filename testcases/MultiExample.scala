import scala.collection.immutable.Set
import scala.collection.immutable.Multiset

object MultisetOperations {

  def disjointUnion1(a: Multiset[Int], b: Multiset[Int]) : Multiset[Int] = {
    a +++ b
  } ensuring(res => res.size == a.size + b.size)

  def preservedUnderToSet1(a: Multiset[Int], b: Multiset[Int]) : Multiset[Int] = {
    a ++ b
  } ensuring(res => res.toSet == a.toSet ++ b.toSet)

  def preservedUnderToSet2(a: Multiset[Int], b: Multiset[Int]) : Multiset[Int] = {
    a ** b
  } ensuring(res => res.toSet == a.toSet ** b.toSet)

}
