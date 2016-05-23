/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package aspects

import purescala.Expressions.Expr
import purescala.ExprOps.formulaSize
import purescala.TypeOps.isSubtypeOf

/**
 * Informs sub-productions that there are extra terminals available (used by
 * grammars.ExtraTerminals).
 */
case class ExtraTerminals(s: Set[Expr]) extends PersistentAspect {
  def asString(implicit ctx: LeonContext) = {
    s.toList.map(_.asString).mkString("{", ",", "}")
  }


  override def applyTo(lab: Label, ps: Seq[Production])(implicit ctx: LeonContext) = {
    super.applyTo(lab, ps) ++ {
      s.filter(e => isSubtypeOf(e.getType, lab.getType)).map { e =>
        ProductionRule[Label, Expr](Nil, { (es: Seq[Expr]) => e }, Tags.Top, formulaSize(e))
      }
    }
  }
}
