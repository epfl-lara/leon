/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars
package aspects

import purescala.Types._

case class TypeDepthBound(bound: Int) extends PersistentAspect(TypeDepthBoundAspectKind) {
  override def asString(implicit ctx: LeonContext): String = "" // This is just debug pollution to print

  /** Computes the depth of the ADT type, function types have no cost */
  def adtDepth(t: TypeTree): Int = t match {
    case NAryType(Nil, _) =>
      1

    case FunctionType(ats, ret) =>
      (ret +: ats).map(adtDepth).max

    case NAryType(ts, _) =>
      ts.map(adtDepth).max+1
  }

  override def applyTo(lab: Label, ps: Seq[Production])(implicit ctx: LeonContext) = {
    if (adtDepth(lab.getType) > bound) {
      Nil
    } else {
      super.applyTo(lab, ps)
    }
  }

}
