/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.datastructure

import scala.collection.mutable.{Map => MutableMap}

class DisjointSets[T] {
  // A map from elements to their parent and rank
  private var disjTree = MutableMap[T, (T, Int)]()

  private def findInternal(x: T): (T, Int) = {
    val (p, rank) = disjTree(x)
    if (p == x)
      (x, rank)
    else {
      val root = findInternal(p)
      // compress path 
      disjTree(x) = root
      root
    }
  }

  private def findOrCreateInternal(x: T) =
    if (!disjTree.contains(x)) {
      disjTree += (x -> (x, 1))
      (x, 1)
    } else findInternal(x)

  def findOrCreate(x: T) = findOrCreateInternal(x)._1

  def find(x: T) = findInternal(x)._1

  /**
   * Returns true if two sets that not already merged got merged 
   */
  def union(x: T, y: T): Boolean = {
    val (rep1, rank1) = findOrCreateInternal(x)
    val (rep2, rank2) = findOrCreateInternal(y)
    if (rep1 == rep2) false
    else {
      if (rank1 < rank2) {
        disjTree(rep1) = (rep2, rank2)
      } else if (rank2 < rank1) {
        disjTree(rep2) = (rep1, rank1)
      } else
        disjTree(rep1) = (rep2, rank2 + 1)
      true
    }
  }

  /**
   * Returns true if two sets that not already merged got merged
   */
  def union(xs: Seq[T]): Boolean = {
    if (!xs.isEmpty) {
      val (_, r) = xs.tail.foldLeft((xs.head, false)) {
        case ((prev, merged), curr) =>
          val r = union(prev, curr)
          (curr, merged || r)
      }
      r
    } else false
  }

  def toMap = {
    val repToSet = disjTree.keys.foldLeft(MutableMap[T, Set[T]]()) {
      case (acc, k) =>
        val root = find(k)
        if (acc.contains(root))
          acc(root) = acc(root) + k
        else
          acc += (root -> Set(k))
        acc
    }
    disjTree.keys.map {k => (k -> repToSet(find(k)))}.toMap
  }
  
  override def toString = {
    disjTree.toString
  }
}