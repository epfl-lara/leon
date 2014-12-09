/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package repair
import synthesis._

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
      case rules.GuidedDecomp => h/3
      case rules.GuidedCloser => h/3
      case rules.CEGLESS      => h/2
      case _ => h
    })
  }

  def costOfGuide(p: Problem): Int = {
    val TopLevelAnds(clauses) = p.pc

    val guides = clauses.collect {
      case FunctionInvocation(TypedFunDef(fd, _), Seq(expr)) if fullName(fd) == "leon.lang.synthesis.guide" => expr
    }

    guides.map(formulaSize(_)).sum
  }
}
