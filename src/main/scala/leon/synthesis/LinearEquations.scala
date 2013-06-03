/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeNormalizations.linearArithmeticForm
import purescala.TypeTrees._
import purescala.Common._

import synthesis.Algebra._

object LinearEquations {
  // This is a hack, but the use of an evaluator in this file is itself beyond that.
  import evaluators._
  private lazy val evaluator = new DefaultEvaluator(LeonContext(), Program.empty)

  //eliminate one variable from normalizedEquation t + a1*x1 + ... + an*xn = 0
  //return a mapping for each of the n variables in (pre, map, freshVars)
  def elimVariable(as: Set[Identifier], normalizedEquation: List[Expr]): (Expr, List[Expr], List[Identifier]) = {
    require(normalizedEquation.size > 1)
    require(normalizedEquation.tail.forall{case IntLiteral(i) if i != 0 => true case _ => false})
    val t: Expr = normalizedEquation.head
    val coefsVars: List[Int] = normalizedEquation.tail.map{case IntLiteral(i) => i}
    val orderedParams: Array[Identifier] = as.toArray
    val coefsParams: List[Int] = linearArithmeticForm(t, orderedParams).map{case IntLiteral(i) => i}.toList
    //val coefsParams: List[Int] = if(coefsParams0.head == 0) coefsParams0.tail else coefsParams0
    val d: Int = gcd((coefsParams ++ coefsVars).toSeq)

    if(coefsVars.size == 1) {
      val coef = coefsVars.head
      (Equals(Modulo(t, IntLiteral(coef)), IntLiteral(0)), List(UMinus(Division(t, IntLiteral(coef)))), List())
    } else if(d > 1) {
      val newCoefsParams: List[Expr] = coefsParams.map(i => IntLiteral(i/d) : Expr)
      val newT = newCoefsParams.zip(IntLiteral(1)::orderedParams.map(Variable(_)).toList).foldLeft[Expr](IntLiteral(0))((acc, p) => Plus(acc, Times(p._1, p._2)))
      elimVariable(as, newT :: normalizedEquation.tail.map{case IntLiteral(i) => IntLiteral(i/d) : Expr})
    } else {
      val basis: Array[Array[Int]]  = linearSet(as, normalizedEquation.tail.map{case IntLiteral(i) => i}.toArray)
      val (pre, sol) = particularSolution(as, normalizedEquation)
      val freshVars: Array[Identifier] = basis(0).map(_ => FreshIdentifier("v", true).setType(Int32Type))

      val tbasis = basis.transpose
      assert(freshVars.size == tbasis.size)
      val basisWithFreshVars: Array[Array[Expr]] = freshVars.zip(tbasis).map{
        case (lambda, column) => column.map((i: Int) => Times(IntLiteral(i), Variable(lambda)): Expr)
      }.transpose
      val combinationBasis: Array[Expr] = basisWithFreshVars.map((v: Array[Expr]) => v.foldLeft[Expr](IntLiteral(0))((acc, e) => Plus(acc, e)))
      assert(combinationBasis.size == sol.size)
      val subst: List[Expr] = sol.zip(combinationBasis.toList).map(p => Plus(p._1, p._2): Expr)

      (pre, subst, freshVars.toList)
    }

  }

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
        else if(i == j) {
          K(j)(j) = gcd(coef.drop(j+1))/gcd(coef.drop(j))
        }
      }
    }
    for(j <- 0 until K.size - 1) {
      val (_, sols) = particularSolution(as, IntLiteral(coef(j)*K(j)(j)) :: coef.drop(j+1).map(IntLiteral(_)).toList)
      var i = 0
      while(i < sols.size) {
        // seriously ??? 
        K(i+j+1)(j) = evaluator.eval(sols(i)).asInstanceOf[EvaluationResults.Successful].value.asInstanceOf[IntLiteral].value
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
    val normalized: Array[Expr] = linearArithmeticForm(Minus(lhs, rhs), orderedXs)
    val (pre, sols) = particularSolution(as, normalized.toList)
    (pre, orderedXs.zip(sols).toMap)
  }

  //return a particular solution to t + c1x + c2y = 0, with (pre, (x0, y0))
  def particularSolution(as: Set[Identifier], t: Expr, c1: Expr, c2: Expr): (Expr, (Expr, Expr)) = {
    val (IntLiteral(i1), IntLiteral(i2)) = (c1, c2)
    val (v1, v2) = extendedEuclid(i1, i2)
    val d = gcd(i1, i2)

    val pre = Equals(Modulo(t, IntLiteral(d)), IntLiteral(0))

    (pre,
     (
       UMinus(Times(IntLiteral(v1), Division(t, IntLiteral(d)))),
       UMinus(Times(IntLiteral(v2), Division(t, IntLiteral(d))))
     )
    )
  }

  //the equation must at least contain the term t and one variable
  def particularSolution(as: Set[Identifier], normalizedEquation: List[Expr]): (Expr, List[Expr]) = {
    require(normalizedEquation.size >= 2)
    val t: Expr = normalizedEquation.head
    val coefs: List[Int] = normalizedEquation.tail.map{case IntLiteral(i) => i}
    val d = gcd(coefs.toSeq)
    val pre = Equals(Modulo(t, IntLiteral(d)), IntLiteral(0))

    if(normalizedEquation.size == 2) {
      (pre, List(UMinus(Division(t, normalizedEquation(1)))))
    } else if(normalizedEquation.size == 3) {
      val (_, (w1, w2)) = particularSolution(as, t, normalizedEquation(1), normalizedEquation(2))
      (pre, List(w1, w2))
    } else {
      val gamma1: Expr = normalizedEquation(1)
      val coefs: List[Int] = normalizedEquation.drop(2).map{case IntLiteral(i) => i}
      val gamma2: Expr = IntLiteral(gcd(coefs.toSeq))
      val (_, (w1, w)) = particularSolution(as, t, gamma1, gamma2)
      val (_, sols) = particularSolution(as, UMinus(Times(w, gamma2)) :: normalizedEquation.drop(2))
      (pre, w1 :: sols)
    }

  }
}
