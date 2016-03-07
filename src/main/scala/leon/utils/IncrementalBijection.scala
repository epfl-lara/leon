/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

class IncrementalBijection[A,B] extends Bijection[A,B] with IncrementalState {
  private var a2bStack = List[Map[A,B]]()
  private var b2aStack = List[Map[B,A]]()

  private def recursiveGet[T,U](stack: List[Map[T,U]], t: T): Option[U] = stack match {
    case t2u :: xs => t2u.get(t) orElse recursiveGet(xs, t)
    case Nil => None
  }

  override def getA(b: B) = b2a.get(b) match {
    case s @ Some(a) => s
    case None => recursiveGet(b2aStack, b)
  }

  override def getB(a: A) = a2b.get(a) match {
    case s @ Some(b) => s
    case None => recursiveGet(a2bStack, a)
  }

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
    a2bStack = Nil
    b2aStack = Nil
  }

  def push(): Unit = {
    a2bStack = a2b :: a2bStack
    b2aStack = b2a :: b2aStack
    a2b = Map()
    b2a = Map()
  }

  def pop(): Unit = {
    a2b = a2bStack.head
    b2a = b2aStack.head
    a2bStack = a2bStack.tail
    b2aStack = b2aStack.tail
  }

}
