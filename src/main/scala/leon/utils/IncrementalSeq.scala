/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.Stack
import scala.collection.mutable.Builder
import scala.collection.mutable.ArrayBuffer
import scala.collection.{Iterable, IterableLike}

class IncrementalSeq[A] extends IncrementalState
                        with Iterable[A]
                        with IterableLike[A, Seq[A]]
                        with Builder[A, IncrementalSeq[A]] {

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

  def iterator = stack.flatten.iterator
  def +=(e: A) = { stack.head += e; this }

  override def newBuilder = new scala.collection.mutable.ArrayBuffer()
  def result = this

  push()
}
