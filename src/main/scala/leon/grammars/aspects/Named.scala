/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package aspects

case class Named(name: String) extends Aspect {

  def applyTo(l: Label, ps: Seq[Production])(implicit ctx: LeonContext) = {
    ps
  }

  def asString(implicit ctx: LeonContext) = "("+name+")"
}
