package leon
package utils

import scala.collection.mutable

class DedupedPriorityQueue[A, K](key: A => K)(implicit val ordering: Ordering[A]) {

  private val queue = new mutable.PriorityQueue[A]()(ordering)
  private val dedupingSet = new mutable.HashSet[K]()

  def isEmpty: Boolean = queue.isEmpty
  def nonEmpty: Boolean = queue.nonEmpty
  def size: Int = queue.size

  def enqueue(a: A) = {
    val k = key(a)
    if (!dedupingSet(k)) {
      queue.enqueue(a)
      dedupingSet.add(k)
    }
  }

  def enqueueAll(as: Seq[A]) = as.foreach(enqueue)

  def dequeue(): A = queue.dequeue()
  def head: A = queue.head

  def clear() = {
    queue.clear()
    dedupingSet.clear()
  }

}
