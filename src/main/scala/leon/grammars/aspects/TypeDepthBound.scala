/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars
package aspects

import purescala.TypeOps.depth

case class TypeDepthBound(bound: Int) extends PersistentAspect {
  override def asString(implicit ctx: LeonContext): String = "" // This is just debug pollution to print

  override def applyTo(lab: Label, ps: Seq[Production])(implicit ctx: LeonContext) = {
    if (depth(lab.getType) > bound) Nil
    else super.applyTo(lab, ps)
  }

}
