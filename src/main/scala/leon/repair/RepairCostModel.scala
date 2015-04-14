/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package repair
import synthesis._

import synthesis.rules._
import repair.rules._

case class RepairCostModel(cm: CostModel) extends WrappedCostModel(cm, "Repair("+cm.name+")") {
  import graph._

  override def andNode(an: AndNode, subs: Option[Seq[Cost]]) = {
    val h = cm.andNode(an, subs).minSize

    Cost(an.ri.rule match {
      case GuidedDecomp => 1
      case GuidedCloser => 0
      case CEGLESS      => 0
      case TEGLESS      => 1
      case _ => h+1
    })
  }
}
