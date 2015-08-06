/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.{Stack, Map => MMap}

class IncrementalMap[A, B] extends IncrementalState {
  private[this] val stack = new Stack[MMap[A, B]]()

  def clear(): Unit = {
    stack.clear()
  }

  def reset(): Unit = {
    clear()
    push()
  }

  def push(): Unit = {
    val last = if (stack.isEmpty) {
      MMap[A,B]()
    } else {
      MMap[A,B]() ++ stack.head
    }
    stack.push(last)
  }

  def pop(): Unit = {
    stack.pop()
  }

  def +=(a: A, b: B): Unit = {
    stack.head += a -> b
  }

  def ++=(as: Traversable[(A, B)]): Unit = {
    stack.head ++= as
  }

  def toMap = stack.head

  push()
}
