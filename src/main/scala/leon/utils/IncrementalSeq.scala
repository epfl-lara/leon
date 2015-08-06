/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.Stack
import scala.collection.mutable.ArrayBuffer

class IncrementalSeq[A] extends IncrementalState {
  private[this] val stack = new Stack[ArrayBuffer[A]]()

  def clear() : Unit = {
    stack.clear()
  }

  def reset(): Unit = {
    clear()
    push()
  }

  def push(): Unit = {
    stack.push(new ArrayBuffer())
  }

  def pop(): Unit = {
    stack.pop()
  }

  def +=(e: A): Unit = {
    stack.head += e
  }

  def toSeq = stack.toSeq.flatten

  push()
}
