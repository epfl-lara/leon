package parsable

object IntSets {
  import scala.collection.immutable.Set

  def union(s1: Set[Int], s2: Set[Int]): Set[Int] = {
    require(!s1.isEmpty && !s2.isEmpty)
    s1 ++ s2
  } ensuring((res: Set[Int]) => res.size > s1.size && res.size > s2.size && res.size <= s1.size + s2.size)

  def main(args: Array[String]): Unit = {
    println(union(Set(1, 2, 3), Set(2, 3, 4)))
  }
}
