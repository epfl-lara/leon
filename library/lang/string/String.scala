/* Copyright 2009-2015 EPFL, Lausanne */

package leon.lang.string

import leon.annotation._

@library
case class String(chars: leon.collection.List[Char]) {
  def +(that: String): String = {
    String(this.chars ++ that.chars)
  }

  def size = chars.size

  def length = size
}
