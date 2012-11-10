package leon
package synthesis

import leon.purescala.Trees._
import leon.purescala.Common._

// Defines a synthesis triple of the form:
// ⟦ as ⟨ C | phi ⟩ xs ⟧
case class Problem(as: List[Identifier], c: Expr, phi: Expr, xs: List[Identifier]) {
  override def toString = "⟦ "+as.mkString(";")+" ⟨ "+c+" | "+phi+" ⟩ "+xs.mkString(";")+" ⟧ "

  val complexity: ProblemComplexity = ProblemComplexity(this)
}
