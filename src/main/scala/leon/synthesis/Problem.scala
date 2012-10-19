package leon
package synthesis

import leon.purescala.Trees._
import leon.purescala.Common._

// Defines a synthesis triple of the form:
// ⟦ as ⟨ phi ⟩ xs ⟧
case class Problem(as: Set[Identifier], phi: Expr, xs: Set[Identifier]) {
  override def toString = "⟦ "+as.mkString(";")+" ⟨ "+phi+" ⟩ "+xs.mkString(";")+" ⟧ "
}
