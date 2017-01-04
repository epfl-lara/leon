/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package aspects

import purescala.Types._

case class RealTyped(tpe: TypeTree) extends Aspect(RealTypedAspectKind) {

  def applyTo(l: Label, ps: Seq[Production])(implicit ctx: LeonContext) = {
    ps
  }

  def asString(implicit ctx: LeonContext) = "("+tpe.asString+")"
}
