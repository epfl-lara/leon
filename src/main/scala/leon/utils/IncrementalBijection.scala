/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.{Map => MutableMap, Stack}

class IncrementalBijection[A,B] extends Bijection[A,B] with IncrementalState {
  protected val a2bStack = Stack[MutableMap[A,B]]()
  protected val b2aStack = Stack[MutableMap[B,A]]()

  override def getA(b: B) = b2a.get(b) match {
    case s @ Some(a) => s
    case None => b2aStack.view.flatMap(_.get(b)).headOption
  }

  override def getB(a: A) = a2b.get(a) match {
    case s @ Some(b) => s
    case None => a2bStack.view.flatMap(_.get(a)).headOption
  }

  override def iterator = aToB.iterator

  def aToB: Map[A,B] = {
    a2bStack.reverse.foldLeft(Map[A,B]()) { _ ++ _ } ++ a2b
  }

  def bToA: Map[B,A] = {
    b2aStack.reverse.foldLeft(Map[B,A]()) { _ ++ _ } ++ b2a
  }

  override def containsA(a: A) = getB(a).isDefined
  override def containsB(b: B) = getA(b).isDefined

  override def aSet = a2b.keySet ++ a2bStack.flatMap(_.keySet)
  override def bSet = b2a.keySet ++ b2aStack.flatMap(_.keySet)

  def reset() : Unit = {
    super.clear()
    a2bStack.clear()
    b2aStack.clear()
  }

  def push(): Unit = {
    a2bStack.push(a2b.clone)
    b2aStack.push(b2a.clone)
    a2b.clear()
    b2a.clear()
  }

  def pop(): Unit = {
    a2b.clear()
    a2b ++= a2bStack.head
    b2a.clear()
    b2a ++= b2aStack.head
    a2bStack.pop()
    b2aStack.pop()
  }

  override def swap: IncrementalBijection[B, A] = new IncrementalBijection[B, A] {
    override protected val a2b = IncrementalBijection.this.b2a
    override protected val b2a = IncrementalBijection.this.a2b
    override protected val a2bStack = IncrementalBijection.this.b2aStack
    override protected val b2aStack = IncrementalBijection.this.a2bStack
  }
}
