package leon.synthesis

import leon.purescala.Trees._
import leon.purescala.Common._

object LinearEquations {

  //eliminate one variable from normalizedEquation t + a1*x1 + ... + an*xn = 0
  //return a mapping for each of the n variables in (pre, map, freshVars)
  //def elimVariable(as: Set[Identifier], xs: , normalizedEquation: List[Expr]): (Expr, List[Expr], List[Identifier]) {
  //  val t: Expr = normalizedEquation.head
  //  val coefsVars: List[Int] = normalizedEquation.tail.map{case IntLiteral(i) => i}
  //  val orderedParams: Array[Identifier] = as.toArray
  //  val coefsParams: List[Int] = ArithmeticNormalization(t, orderedAs).map{case IntLiteral(i) => i}
  //  val d = GCD.gcd((coefsParams.tail ++ coefs).toSeq)
  //  if(d > 1) 


  //  val pre = Equals(Modulo(t, IntLiteral(d)), IntLiteral(0))

  //}


  //compute a list of solution of the equation c1*x1 + ... + cn*xn where coef = [c1 ... cn]
  //return the solution in the form of a list of n-1 vectors that form a basis for the set
  //of solutions, that is res=(v1, ..., v{n-1}) and any solution x* to the original solution
  //is a linear combination of the vi's
  //Intuitively, we are building a "basis" for the "vector space" of solutions (although we are over
  //integers, so it is not a vector space).
  //we are returning a matrix where the columns are the vectors
  def linearSet(as: Set[Identifier], coef: Array[Int]): Array[Array[Int]] = {

    val K = Array.ofDim[Int](coef.size, coef.size-1)
    for(i <- 0 until K.size) {
      for(j <- 0 until K(i).size) {
        if(i < j)
          K(i)(j) = 0
        else if(i == j)
          K(j)(j) = GCD.gcd(coef.drop(j+1))/GCD.gcd(coef.drop(j))
      }
    }
    for(j <- 0 until K.size - 1) {
      val (_, sols) = particularSolution(as, IntLiteral(-coef(j)*K(j)(j)) :: coef.drop(j+1).map(IntLiteral(_)).toList)
      assert(sols.size == K.size - j)
      var i = 0
      while(i < sols.size) {
        K(i+j+1)(j) = sols(i).asInstanceOf[IntLiteral].value
        i += 1
      }
    }

    K
  }

  //as are the parameters while xs are the variable for which we want to find one satisfiable assignment
  //return (pre, sol) with pre a precondition under which sol is a solution mapping to the xs
  def particularSolution(as: Set[Identifier], xs: Set[Identifier], equation: Equals): (Expr, Map[Identifier, Expr]) = {
    val lhs = equation.left
    val rhs = equation.right
    val orderedXs = xs.toArray
    val normalized: Array[Expr] = ArithmeticNormalization(Minus(lhs, rhs), orderedXs)
    val (pre, sols) = particularSolution(as, normalized.toList)
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

  def particularSolution(as: Set[Identifier], normalizedEquation: List[Expr]): (Expr, List[Expr]) = {
    val t: Expr = normalizedEquation.head
    val coefs: List[Int] = normalizedEquation.tail.map{case IntLiteral(i) => i}
    val d = GCD.gcd(coefs.toSeq)
    val pre = Equals(Modulo(t, IntLiteral(d)), IntLiteral(0))

    if(normalizedEquation.size == 3) {
      val (_, (w1, w2)) = particularSolution(as, t, normalizedEquation(1), normalizedEquation(2))
      (pre, List(w1, w2))
    } else {

      val gamma1: Expr = normalizedEquation(1)
      val coefs: List[Int] = normalizedEquation.drop(2).map{case IntLiteral(i) => i}
      val gamma2: Expr = IntLiteral(GCD.gcd(coefs.toSeq))
      val (_, (w1, w)) = particularSolution(as, t, gamma1, gamma2)
      val (_, sols) = particularSolution(as, Minus(IntLiteral(0), Times(w, gamma2)) :: normalizedEquation.drop(2))
      (pre, w1 :: sols)
    }

  }
}
