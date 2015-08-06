/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.{Stack, Set => MSet}

class IncrementalSet[A] extends IncrementalState {
  private[this] val stack = new Stack[MSet[A]]()

  def clear(): Unit = {
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

  def +=(a: A): Unit = {
    stack.head += a
  }

  def ++=(as: Traversable[A]): Unit = {
    stack.head ++= as
  }

  def toSet = stack.toSet.flatten

  push()
}
