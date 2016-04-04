/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package aspects

import utils.SeqUtils._

/**
 * Attach sizes to labels and transmit them down accordingly
 */
case class Sized(size: Int) extends Aspect {
  def asString(implicit ctx: LeonContext) = "|"+size+"|"

  def applyTo(lab: Label, ps: Seq[Production])(implicit ctx: LeonContext) = {
    val optimizeCommut = true

    ps.flatMap { p =>
      if (size <= 0) {
        Nil
      } else if (p.arity == 0) {
        if (size == p.cost) {
          List(p)
        } else {
          Nil
        }
      } else {
        val sizes = if(optimizeCommut && Tags.isCommut(p.tag) && p.subTrees.toSet.size == 1) {
          sumToOrdered(size - p.cost, p.arity)
        } else {
          sumTo(size - p.cost, p.arity)
        }

        for (ss <- sizes) yield {
          val newSubTrees = (p.subTrees zip ss).map {
            case (lab, s) => lab.withAspect(Sized(s))
          }

          ProductionRule(newSubTrees, p.builder, p.tag, p.cost)
        }
      }
    }
  }
}
