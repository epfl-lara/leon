/* Copyright 2009-2015 EPFL, Lausanne */

package leon.lang

import leon.annotation._
import leon.collection._
import scala.language.implicitConversions

import scala.collection.immutable.{List => ScalaList}

package object string {
  @ignore
  implicit def strToStr(s: java.lang.String): leon.lang.string.String = {
    String(listToList(s.toList))
  }

  @ignore
  def listToList[A](s: ScalaList[A]): List[A] = s match {
    case scala.::(h, t) =>
      Cons(h, listToList(t))
    case _ =>
      Nil[A]()
  }
}
