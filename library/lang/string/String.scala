/* Copyright 2009-2015 EPFL, Lausanne */

package leon.lang.string

import leon.annotation._
import leon.collection._

@library
case class String(chars: List[Char]) {
  def +(that: String): String = {
    String(this.chars ++ that.chars)
  }

  def size = chars.size

  def length = size

  @ignore
  override def toString = {

    "\""+charsToString(chars)+"\""
  }
  @ignore
  def charsToString(chars: List[Char]): java.lang.String = chars match {
    case Cons(h, t) => h + charsToString(t)
    case Nil() => ""
  }
}
