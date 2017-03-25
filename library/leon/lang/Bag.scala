/* Copyright 2009-2016 EPFL, Lausanne */

package leon.lang

import leon.annotation._
import scala.Boolean
import scala.Predef.{augmentString,ArrowAssoc,String}

object Bag {
  @library
  def empty[T] = Bag[T]()

  @ignore
  def apply[T](elems: (T, scala.math.BigInt)*) = {
    new Bag[T](scala.collection.immutable.Map[T, scala.math.BigInt](elems : _*))
  }
  
  @extern @library
  def mkString[A](bag: Bag[A], infix: String, f: A => String) = {
    bag.theBag.flatMap{ case (k, v) => 
      scala.collection.immutable.List.range(1, v.toString.toInt).map(_ => f(k))
    }.toList.sorted.mkString(infix)
  }
}

@ignore
case class Bag[T](theBag: scala.collection.immutable.Map[T, scala.math.BigInt]) {
  def +(a: T): Bag[T] = new Bag(theBag + (a -> (theBag.getOrElse(a, scala.math.BigInt(0)) + 1)))
  def ++(that: Bag[T]): Bag[T] = new Bag[T]((theBag.keys ++ that.theBag.keys).toSet.map { (k: T) =>
    k -> (theBag.getOrElse(k, scala.math.BigInt(0)) + that.theBag.getOrElse(k, scala.math.BigInt(0)))
  }.toMap)

  def --(that: Bag[T]): Bag[T] = new Bag[T](theBag.flatMap { case (k,v) =>
    val res = v - that.get(k)
    if (res <= 0) scala.collection.immutable.Nil else scala.collection.immutable.List(k -> res)
  })

  def &(that: Bag[T]): Bag[T] = new Bag[T](theBag.flatMap { case (k,v) =>
    val res = v min that.get(k)
    if (res <= 0) scala.collection.immutable.Nil else scala.collection.immutable.List(k -> res)
  })

  def get(a: T): scala.math.BigInt = theBag.getOrElse(a, scala.math.BigInt(0))
  def apply(a: T): scala.math.BigInt = get(a)
  def isEmpty: Boolean = theBag.isEmpty
}

