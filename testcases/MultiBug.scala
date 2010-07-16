import scala.collection.immutable.Set
import scala.collection.immutable.Multiset

object MultisetOperations {

  def disjointUnion2(a: Multiset[Int], b: Multiset[Int]) : Multiset[Int] = {
    a +++ b
  } ensuring(res => res.toSet == (a.toSet ++ b.toSet))

}
