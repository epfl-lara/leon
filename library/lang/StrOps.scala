/* Copyright 2009-2016 EPFL, Lausanne */

package leon.lang

import leon.annotation._

/**
 * @author Mikael
 */
object StrOps {
  @ignore
  def concat(a: String, b: String): String = {
    a + b
  }
  @internal @library
  def escape(s: String): String = s // Wrong definition, but it will eventually use StringEscapeUtils.escapeJava(s) at parsing and compile time.
}