/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package repair
import synthesis._

import synthesis.rules._
import repair.rules._

import purescala.Definitions._
import purescala.Trees._
import purescala.DefOps._
import purescala.TreeOps._
import purescala.Extractors._

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

  override def rulesFor(sctx: SynthesisContext, on: OrNode) = {
    val rs = cm.rulesFor(sctx, on)

    on.parent match {
      case None =>
        GuidedDecomp +: rs
      case Some(an: AndNode) if an.ri.rule == GuidedDecomp =>
        GuidedCloser +: rs
      case _ =>
        rs
    }
  }
}
