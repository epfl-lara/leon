package leon.synthesis

import leon.purescala.Trees._
import leon.purescala.Common._

object LinearEquations {

  //as are the parameters while xs are the variable for which we want to find one satisfiable assignment
  def particularSolution(as: Set[Identifier], xs: Set[Identifier], equation: Equals): Map[Identifier, Expr] = {
    val lhs = equation.left
    val rhs = equation.right
    val normalized: Array[Expr] = ArithmeticNormalization(Minus(lhs, rhs), xs.toArray)
    particularSolution(as, xs, normalized)
  }

  def particularSolution(as: Set[Identifier], xs: Set[Identifier], normalizedEquation: Array[Expr]): Map[Identifier, Expr] = {
    println("normalized expression: " + normalizedEquation.mkString(" + "))

    assert(normalizedEquation.size == 1 + xs.size)
    //let's assume for now that we have at most two variables

    null

  }
}
