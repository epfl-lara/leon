/* Copyright 2009-2016 EPFL, Lausanne */

package leon.lang

import leon.annotation._
import scala.Predef.String

/**
 * @author Mikael
 */
object StrOps {
  @ignore
  def concat(a: String, b: String): String = {
    a + b
  }
  @ignore
  def bigLength(s: String): scala.math.BigInt = {
    scala.math.BigInt(s.length)
  }
  @ignore
  def bigSubstring(s: String, start: scala.math.BigInt, end: scala.math.BigInt): String = {
    s.substring(start.toInt, end.toInt)
  }
  @internal @library
  def escape(s: String): String = s // Wrong definition, but it will eventually use StringEscapeUtils.escapeJava(s) at parsing and compile time.
}