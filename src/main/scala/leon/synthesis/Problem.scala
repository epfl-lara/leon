package leon
package synthesis

import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.Common._

// Defines a synthesis triple of the form:
// ⟦ as ⟨ C | phi ⟩ xs ⟧
case class Problem(as: List[Identifier], c: Expr, phi: Expr, xs: List[Identifier]) {
  override def toString = "⟦ "+as.mkString(";")+", "+c+" ᚒ  ⟨ "+phi+" ⟩ "+xs.mkString(";")+" ⟧ "

  val complexity: ProblemComplexity = ProblemComplexity(this)
}

object Problem {
  def fromChoose(ch: Choose): Problem = {
    val xs = ch.vars
    val phi = ch.pred
    val as = (variablesOf(phi)--xs).toList

    Problem(as, BooleanLiteral(true), phi, xs)
  }
}
