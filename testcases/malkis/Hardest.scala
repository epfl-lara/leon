import scala.collection.immutable.Set

object Hardest {
  def vc(
    thread : Set[Int],
    thread_A : Set[Int],
    thread_A_2 : Set[Int],
    thread_B_3 : Set[Int],
    thread_C_2 : Set[Int],
    thread_count : Int,
    thread_count_2 : Int,
    thread_t : Int,
    thread_t_1 : Int,
    nulll : Int
  ) : Boolean = {
    require(
         thread_B_3.contains(thread_t_1)
      && (thread_C_2 == Set.empty[Int] || 0 == 0)
      && (thread_B_3 ** thread_C_2) == Set.empty[Int]
      && (thread_A_2 ** thread_C_2) == Set.empty[Int]
      && (thread_A_2 ** thread_B_3) == Set.empty[Int]
      && ((thread_A_2 ++ thread_B_3 ++ thread_C_2) subsetOf thread)
      && (thread_A_2.size <= 0)
      && !thread.contains(nulll)
      && (thread_A subsetOf thread)
      && (thread_A.size <= thread_count)
      && thread.contains(thread_t)
    )
    ((thread_A_2 ++ (thread_B_3 -- Set(thread_t_1))) ++
     (thread_C_2 ++ Set(thread_t_1))) subsetOf thread
  } ensuring(res => res)
}
