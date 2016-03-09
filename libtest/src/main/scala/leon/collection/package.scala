/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import leon.annotation._
import leon.collection.List
import leon.lang._
import leon.lang.synthesis.choose

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

}
