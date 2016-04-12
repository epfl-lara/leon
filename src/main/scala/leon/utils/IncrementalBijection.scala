/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.{Map => MutableMap, Stack}

/** Extends a Bijection with incremental (push/pop) features
  *
  * This maintains a stack of frames, at each frame there is
  * a bijection. When pushing a new frame, the previous mapping
  * are kept, but new mappings only happen in the current frame,
  * which means that on the next pop, only the additional mapping
  * at this frame level will be removed from the structure.
  *
  * Useful when you have a stack structure for your process and
  * want to be able to do some modification to the bijection and then
  * come back to the original bijection later.
  */
class IncrementalBijection[A,B] extends Bijection[A,B] with IncrementalState {
  protected val a2bStack = Stack[MutableMap[A,B]]()
  protected val b2aStack = Stack[MutableMap[B,A]]()

  /** Returns the corresponding A
    *
    * If b is not mapped to an element in the current frame
    * then this will find the element in the most recent frame
    */
  override def getA(b: B) = b2a.get(b)

  /** Returns the corresponding B
    *
    * If a is not mapped to an element in the current frame
    * then this will find the element deeper in the stack, if
    * it exists.
    */
  override def getB(a: A) = a2b.get(a)


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

  /** Clears the entire IncrementalBijection */
  def reset() : Unit = {
    super.clear()
    a2bStack.clear()
    b2aStack.clear()
  }

  /** Add a new frame of bijection */
  def push(): Unit = {
    a2bStack.push(a2b.clone)
    b2aStack.push(b2a.clone)
  }

  /** Remove the latest frame of bijection */
  def pop(): Unit = {
    a2b.clear()
    a2b ++= a2bStack.head
    b2a.clear()
    b2a ++= b2aStack.head
    a2bStack.pop()
    b2aStack.pop()
  }

  /** Return an IncrementalBijection in the other direction
    *
    * The returned bijection remains linked to the original, which
    * means that any push/pop on any of the two bijection should be
    * visible in both, same goes for new mappings added.
    */
  override def swap: IncrementalBijection[B, A] = new IncrementalBijection[B, A] {
    override protected val a2b = IncrementalBijection.this.b2a
    override protected val b2a = IncrementalBijection.this.a2b
    override protected val a2bStack = IncrementalBijection.this.b2aStack
    override protected val b2aStack = IncrementalBijection.this.a2bStack
  }
}
