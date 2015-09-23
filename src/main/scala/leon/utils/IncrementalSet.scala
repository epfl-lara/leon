/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.{Stack, Set => MSet}
import scala.collection.mutable.Builder
import scala.collection.{Iterable, IterableLike, GenSet}

class IncrementalSet[A] extends IncrementalState
                        with Iterable[A]
                        with IterableLike[A, Set[A]]
                        with Builder[A, IncrementalSet[A]] {

  private[this] val stack = new Stack[MSet[A]]()
  override def repr = stack.flatten.toSet

  override def clear(): Unit = {
    stack.clear()
  }

  def reset(): Unit = {
    clear()
    push()
  }

  def push(): Unit = {
    stack.push(MSet())
  }

  def pop(): Unit = {
    stack.pop()
  }

  def apply(elem: A) = repr.contains(elem)
  def contains(elem: A) = repr.contains(elem)

  def iterator = stack.flatten.iterator
  def += (elem: A) = { stack.head += elem; this }
  def -= (elem: A) = { stack.foreach(_ -= elem); this }

  override def newBuilder = new scala.collection.mutable.SetBuilder(Set.empty[A])
  def result = this

  push()
}
