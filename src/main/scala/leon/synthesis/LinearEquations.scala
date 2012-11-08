package leon.synthesis

import leon.purescala.Trees._
import leon.purescala.Common._

object LinearEquations {

  //as are the parameters while xs are the variable for which we want to find one satisfiable assignment
  //return (pre, sol) with pre a precondition under which sol is a solution mapping to the xs
  def particularSolution(as: Set[Identifier], xs: Set[Identifier], equation: Equals): (Expr, Map[Identifier, Expr]) = {
    val lhs = equation.left
    val rhs = equation.right
    val orderedXs = xs.toArray
    val normalized: Array[Expr] = ArithmeticNormalization(Minus(lhs, rhs), orderedXs)
    val (pre, sols) = particularSolution(as, normalized)
    (pre, orderedXs.zip(sols).toMap)
  }

  //return a particular solution to t + c1x + c2y = 0, with (pre, (x0, y0))
  def particularSolution(as: Set[Identifier], t: Expr, c1: Expr, c2: Expr): (Expr, (Expr, Expr)) = {
    val (IntLiteral(i1), IntLiteral(i2)) = (c1, c2)
    val (v1, v2) = GCD.extendedEuclid(i1, i2)
    val d = GCD.gcd(i1, i2)

    val pre = Equals(Modulo(t, IntLiteral(d)), IntLiteral(0))

    (pre,
     (
       Minus(IntLiteral(0), Times(IntLiteral(v1), Division(t, IntLiteral(d)))),
       Minus(IntLiteral(0), Times(IntLiteral(v2), Division(t, IntLiteral(d))))
     )
    )
  }

  def particularSolution(as: Set[Identifier], normalizedEquation: Array[Expr]): (Expr, Array[Expr]) = {
    if(normalizedEquation.size == 3) {
      val (pre, (w1, w2)) = particularSolution(as, normalizedEquation(0), normalizedEquation(1), normalizedEquation(2))
      (pre, Array(w1, w2))
    } else {

      null
    }

  }
}
