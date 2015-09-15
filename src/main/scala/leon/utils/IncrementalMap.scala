/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.{Stack, Map => MMap, Builder}
import scala.collection.generic.Shrinkable
import scala.collection.IterableLike

class IncrementalMap[A, B] private(dflt: Option[B])
  extends IncrementalState
     with Iterable[(A,B)]
     with IterableLike[(A,B), Map[A,B]]
     with Builder[(A,B), IncrementalMap[A, B]]
     with Shrinkable[A]
     with (A => B) {

  def this() = this(None)

  private val stack = new Stack[MMap[A, B]]()

  override def clear(): Unit = {
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

    val withDefault = dflt match {
      case Some(value) => last.withDefaultValue(value)
      case None => last
    }

    stack.push(withDefault)
  }

  def pop(): Unit = {
    stack.pop()
  }

  def withDefaultValue[B1 >: B](dflt: B1) = {
    val map = new IncrementalMap[A, B1](Some(dflt))
    map.stack.pop()
    for (s <- stack.toList) map.stack.push(MMap[A,B1]().withDefaultValue(dflt) ++ s)
    map
  }

  def get(k: A) = stack.head.get(k)
  def apply(k: A) = stack.head.apply(k)
  def contains(k: A) = stack.head.contains(k)
  def isDefinedAt(k: A) = stack.head.isDefinedAt(k)
  def getOrElse[B1 >: B](k: A, e: => B1) = stack.head.getOrElse(k, e)
  def values = stack.head.values

  def iterator = stack.head.iterator
  def +=(kv: (A, B)) = { stack.head += kv; this }
  def -=(k: A) = { stack.head -= k; this }

  override def seq = stack.head.seq
  override def newBuilder = new scala.collection.mutable.MapBuilder(Map.empty[A,B])
  def result = this

  push()
}
