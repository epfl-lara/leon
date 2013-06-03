/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.Common._

// Defines a synthesis triple of the form:
// ⟦ as ⟨ C | phi ⟩ xs ⟧
case class Problem(as: List[Identifier], pc: Expr, phi: Expr, xs: List[Identifier]) {
  override def toString = "⟦ "+as.mkString(";")+", "+(if (pc != BooleanLiteral(true)) pc+" ≺ " else "")+" ⟨ "+phi+" ⟩ "+xs.mkString(";")+" ⟧ "
}

object Problem {
  def fromChoose(ch: Choose, pc: Expr = BooleanLiteral(true)): Problem = {
    val xs = ch.vars
    val phi = ch.pred
    val as = (variablesOf(And(pc, phi))--xs).toList

    Problem(as, pc, phi, xs)
  }
}
