/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package aspects

case class RealTyped(within: Option[(String, Int)]) extends Aspect(RealTypedAspectKind) {

  def applyTo(l: Label, ps: Seq[Production])(implicit ctx: LeonContext) = {
    ps
  }

  def asString(implicit ctx: LeonContext) = within match {
    case None => "{TOPLEVEL}"
    case Some((tp, pos)) =>
      s"{$tp@$pos}"
  }

}
