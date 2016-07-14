/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars
package aspects

/** Limits a grammar by depth */
case class DepthBound(depth: Int) extends Aspect {
  require(depth >= 0)

  def asString(implicit ctx: LeonContext): String = s"D$depth"

  def applyTo(l: Label, ps: Seq[Production])(implicit ctx: LeonContext) = {
    if (depth == 0) Nil
    else if (depth == 1) ps.filter(_.isTerminal)
    else {
      ps map { prod =>
        prod.copy(subTrees = prod.subTrees.map(_.withAspect(DepthBound(depth - 1))))
      }
    }
  }

}
