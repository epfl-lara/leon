/* Copyright 2009-2014 EPFL, Lausanne */
package leon.lang.string

case class String(chars: leon.collection.List[Char]) {
  def +(that: String): String = {
    String(this.chars ++ that.chars)
  }

  def size = chars.size

  def length = size
}
