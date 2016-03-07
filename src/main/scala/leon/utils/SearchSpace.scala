/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

object SearchSpace {

  def reachable[A](sources: Set[A], generateNeighbors: A => Set[A], limit: Option[Int] = None): (Set[A], Boolean) = {
    require(limit forall(_ >= 0))
    def rec(seen: Set[A], toSee: Set[A], limit: Option[Int]): (Set[A], Boolean) = {
      (toSee.headOption, limit) match {
        case (None, _) =>
          (seen, true)
        case (_, Some(0)) =>
          (seen, false)
        case (Some(hd), _) =>
          val neighbors = generateNeighbors(hd)
          rec(seen + hd, toSee ++ neighbors -- (seen + hd), limit map {_ - 1})
      }
    }

    rec(Set(), sources, limit)
  }

}
