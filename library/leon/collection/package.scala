/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import leon.annotation._
import leon.lang._
import leon.lang.synthesis.choose

import scala.collection.Seq
import scala.collection.immutable.Set
import scala.Boolean

package object collection {

  @internal @library
  def setToList[A](set: Set[A]): List[A] = choose { 
    (x: List[A]) => x.content == set
  }

  @library
  def setForall[A](set: Set[A], p: A => Boolean): Boolean = 
    setToList(set).forall(p)

  @library
  def setExists[A](set: Set[A], p: A => Boolean): Boolean =
    setToList(set).exists(p)

  @ignore
  def varargToList[A](elems: Seq[A]): List[A] = {
    var l: List[A] = Nil[A]()
    for (e <- elems) {
      l = Cons(e, l)
    }
    l.reverse
  }
}
