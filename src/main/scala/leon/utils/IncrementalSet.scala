/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.{Stack, Set => MSet}
import scala.collection.mutable.Builder
import scala.collection.{Iterable, IterableLike, GenSet}

/** A stack of mutable sets with a set-like API and methods to push and pop */
class IncrementalSet[A] extends IncrementalState
                        with Iterable[A]
                        with IterableLike[A, Set[A]]
                        with Builder[A, IncrementalSet[A]] {

  private[this] val stack = new Stack[MSet[A]]()
  override def repr = stack.flatten.toSet

  /** Removes all the elements */
  override def clear(): Unit = {
    stack.clear()
  }

  /** Removes all the elements and creates a new set */
  def reset(): Unit = {
    clear()
    push()
  }

  /** Creates one more set level */
  def push(): Unit = {
    stack.push(MSet())
  }

  /** Removes one set level */
  def pop(): Unit = {
    stack.pop()
  }

  /** Returns true if the set contains elem */
  def apply(elem: A) = repr.contains(elem)
  /** Returns true if the set contains elem */
  def contains(elem: A) = repr.contains(elem)

  /** Returns an iterator over all the elements */
  def iterator = stack.flatten.iterator
  /** Add an element to the head set */
  def += (elem: A) = { stack.head += elem; this }
  /** Removes an element from all stacked sets */
  def -= (elem: A) = { stack.foreach(_ -= elem); this }

  override def newBuilder = new scala.collection.mutable.SetBuilder(Set.empty[A])
  def result = this

  push() // By default, creates a new empty mutable set ready to add elements to it.
}
