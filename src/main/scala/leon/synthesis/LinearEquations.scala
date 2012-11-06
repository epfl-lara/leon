package leon.synthesis

import leon.purescala.Trees._
import leon.purescala.Common._

object LinearEquations {

  //as are the parameters while xs are the variable for which we want to find one satisfiable assignment
  def particularSolution(as: Set[Identifier], xs: Set[Identifier], equation: Equals): Map[Identifier, Expr] = {
    val lhs = equation.left
    val rhs = equation.right
    val orderedXs = xs.toArray
    val normalized: Array[Expr] = ArithmeticNormalization(Minus(lhs, rhs), orderedXs)
    particularSolution(as, orderedXs, normalized)
  }

  def particularSolution(as: Set[Identifier], xs: Array[Identifier], normalizedEquation: Array[Expr]): Map[Identifier, Expr] = {
    println("normalized expression: " + normalizedEquation.mkString(" + "))

    assert(normalizedEquation.size == 1 + xs.size)
    //let's assume for now that we have at most two variables

    val t = normalizedEquation(0)
    val (IntLiteral(i1), IntLiteral(i2)) = (normalizedEquation(1), normalizedEquation(2))
    val (v1, v2) = GCD.extendedEuclid(i1, i2)
    val d = GCD.gcd(i1, i2)

    Map(
      xs(0) -> Minus(IntLiteral(0), Times(IntLiteral(v1), Division(t, IntLiteral(d)))),
      xs(1) -> Minus(IntLiteral(0), Times(IntLiteral(v2), Division(t, IntLiteral(d))))
    )

  }
}
