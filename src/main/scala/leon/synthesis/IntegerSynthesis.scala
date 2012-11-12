package leon.synthesis

import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.Common._
import ArithmeticNormalization._
import LinearEquations._

object IntegerSynthesis {

  def apply(as: Set[Identifier], xs: Set[Identifier], formula: Expr): (Expr, List[Expr]) = {
    extractEquals(formula) match {
      case (Some(eq), f) => {
        val vars: Set[Identifier] = variablesOf(eq)
        val eqxs: List[Identifier] = xs.intersect(vars).toList
        println("eqxs: " + eqxs)
        val eqas: Set[Identifier] = as.intersect(vars)
        println("formula: " + formula)
        println("eq: " + eq)
        val normalizedEq: List[Expr] = ArithmeticNormalization(Minus(eq.left, eq.right), eqxs.toArray).toList
        println("normalized eq: " + normalizedEq)
        val (pre, subst, freshVars) = elimVariable(eqas, normalizedEq)
        println("subst: " + subst.mkString("\n"))
        val substMap: Map[Expr, Expr] = eqxs.zip(subst).map{case (id, e) => (Variable(id), e)}.toMap
        val freshFormula = simplify(replace(substMap, f))
        println("fresh formula is: " + freshFormula)
        null
      }
      case (None, f) => null
    }
  }

}
