/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.{Map => MutableMap}

object Bijection {
  def apply[A, B](a: Iterable[(A, B)]): Bijection[A, B] = new Bijection[A, B] ++= a
  def apply[A, B](a: (A, B)*): Bijection[A, B] = apply(a.toSeq)
}

class Bijection[A, B] extends Iterable[(A, B)] {
  protected val a2b = MutableMap[A, B]()
  protected val b2a = MutableMap[B, A]()
  
  def iterator = a2b.iterator

  def +=(a: A, b: B): Unit = {
    a2b += a -> b
    b2a += b -> a
  }

  def +=(t: (A,B)): this.type = {
    +=(t._1, t._2)
    this
  }
  
  def ++=(t: Iterable[(A, B)]) = {
    (this /: t){ case (b, elem) => b += elem }
  }

  def clear(): Unit = {
    a2b.clear()
    b2a.clear()
  }

  def getA(b: B) = b2a.get(b)
  def getB(a: A) = a2b.get(a)
  
  def getAorElse(b: B, orElse: =>A) = b2a.getOrElse(b, orElse)
  def getBorElse(a: A, orElse: =>B) = a2b.getOrElse(a, orElse)

  def toA(b: B) = getA(b).get
  def toB(a: A) = getB(a).get

  def fromA(a: A) = getB(a).get
  def fromB(b: B) = getA(b).get

  def cachedB(a: A)(c: => B) = {
    getB(a).getOrElse {
      val res = c
      this += a -> res
      res
    }
  }

  def cachedA(b: B)(c: => A) = {
    getA(b).getOrElse {
      val res = c
      this += res -> b
      res
    }
  }

  def containsA(a: A) = a2b contains a
  def containsB(b: B) = b2a contains b

  def aSet = a2b.keySet
  def bSet = b2a.keySet
  
  def composeA[C](c: A => C): Bijection[C, B] = {
    new Bijection[C, B] ++= this.a2b.map(kv => c(kv._1) -> kv._2)
  }
  def composeB[C](c: B => C): Bijection[A, C] = {
    new Bijection[A, C] ++= this.a2b.map(kv => kv._1 -> c(kv._2))
  }

  def swap: Bijection[B, A] = new Bijection[B, A] {
    override protected val a2b = Bijection.this.b2a
    override protected val b2a = Bijection.this.a2b
  }
}
