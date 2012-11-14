package leon.synthesis

import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.Common._
import ArithmeticNormalization._
import LinearEquations._

object IntegerSynthesis {

  def apply(as: Set[Identifier], xs: List[Identifier], formula: Expr): (Expr, List[Expr]) = {
    null
    //extractEquals(formula) match {
    //  case (None, f) => (f, xs.map(id => (Variable(id))))
    //  case (Some(eq), f) => {
    //    val vars: Set[Identifier] = variablesOf(eq)
    //    val eqas: Set[Identifier] = as.intersect(vars)

    //    val eqxs: List[Identifier] = xs.toSet.intersect(vars).toList
    //    val ys: Set[Identifier] = xs.toSet.diff(vars)

    //    val normalizedEq: List[Expr] = ArithmeticNormalization(Minus(eq.left, eq.right), eqxs.toArray).toList
    //    val (eqPre, eqWitness, eqFreshVars) = elimVariable(eqas, normalizedEq)

    //    val eqSubstMap: Map[Expr, Expr] = eqxs.zip(eqWitness).map{case (id, e) => (Variable(id), e)}.toMap
    //    val freshFormula = simplify(replace(eqSubstMap, f))
    //    (eqPre, freshFormula)


    //    /*
    //    val (recPre, recSubst) = apply(as, ys ++ eqFreshVars, freshFormula)

    //    val freshPre = simplify(replace(
    //      (ys++freshVars).zip(recSubst).map{
    //        case (id, e) => (Variable(id), e)
    //      }.toMap,
    //      eqPre))

    //    (And(freshPre, recPre), recSubst)
    //    */

    //  }
    //}
  }

}
