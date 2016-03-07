/* Copyright 2009-2015 EPFL, Lausanne */

package leon

/** A trait for objects that can be pretty-printed given a [[leon.LeonContext]] */
trait Printable {
  def asString(implicit ctx: LeonContext): String
}
