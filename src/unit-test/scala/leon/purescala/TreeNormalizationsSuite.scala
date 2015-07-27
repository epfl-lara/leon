/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import leon.purescala.Common._
import leon.purescala.Types._
import leon.purescala.Expressions._
import leon.purescala.TreeNormalizations._

class TreeNormalizationsSuite extends LeonTestSuite with WithLikelyEq with ExpressionsBuilder {

  val xs = Set(xId, yId)
  val as = Set(aId, bId)
  

  test("Single variable isNnf") {
    assert(isNnf(x))
    assert(isNnf(p))
  }
  test("Simple not of a variable isNnf") {
    assert(isNnf(Not(p)))
  }
  test("Not of a boolean literal is not nnf") {
    assert(!isNnf(Not(BooleanLiteral(true))))
  }
  test("Simple combination of literals is nnf") {
    assert(isNnf(And(Not(p), q)))
    assert(isNnf(Or(Not(p), q)))
  }
  test("Top level not is not nnf") {
    assert(!isNnf(Not(And(Not(p), q))))
    assert(!isNnf(Not(Or(Not(p), q))))
  }
  test("Nested structure with only not on leafs is nnf") {
    assert(isNnf(Implies(And(Not(p), q), Or(p, q))))
  }
  test("Nested structure with intermediate Not is not nnf") {
    assert(!isNnf(Implies(Not(And(Not(p), q)), Or(p, q))))
  }



  test("nnf of single variable is itself") {
    assert(nnf(x) === x)
    assert(nnf(p) === p)
  }

  test("nnf of negation of and/or works correctly") {
    val expr1 = Not(And(p, q))
    val res1 = nnf(expr1)
    assert(isNnf(res1))
    assert(res1.isInstanceOf[Or])
    assert(res1.asInstanceOf[Or].exprs.toSet === Set(Not(p), Not(q)))

    val expr2 = Not(Or(p, q))
    val res2 = nnf(expr2)
    assert(isNnf(res2))
    assert(res2.isInstanceOf[And])
    assert(res2.asInstanceOf[And].exprs.toSet === Set(Not(p), Not(q)))
  }

  test("nnf of negation of and/or correctly propagate Not in sub-expressions") {
    val expr1 = Not(And(Not(p), q))
    val res1 = nnf(expr1)
    assert(isNnf(res1))
    assert(res1.isInstanceOf[Or])
    assert(res1.asInstanceOf[Or].exprs.toSet === Set(p, Not(q)))

    val expr2 = Not(Or(p, Not(q)))
    val res2 = nnf(expr2)
    assert(isNnf(res2))
    assert(res2.isInstanceOf[And])
    assert(res2.asInstanceOf[And].exprs.toSet === Set(Not(p), q))
  }



  def checkSameExpr(e1: Expr, e2: Expr, vs: Set[Identifier]) {
    assert( //this outer assert should not be needed because of the nested one
      LikelyEq(e1, e2, vs, BooleanLiteral(true), (e1, e2) => {assert(e1 === e2); true})
    )
  }

  def toSum(es: Seq[Expr]) = es.reduceLeft(Plus)
  def coefToSum(es: Array[Expr], vs: Array[Expr]) = es.zip(Array[Expr](InfiniteIntegerLiteral(1)) ++ vs).foldLeft[Expr](InfiniteIntegerLiteral(0))((acc, p) => Plus(acc, Times(p._1, p._2)))
  
  test("checkSameExpr") {
    checkSameExpr(Plus(x, y), Plus(y, x), xs)
    checkSameExpr(Plus(x, x), Times(x, i(2)), xs)
    checkSameExpr(Plus(x, Plus(x, x)), Times(x, i(3)), xs)
  }

  test("multiply") {
    val lhs = Seq(x, i(2))
    val rhs = Seq(y, i(1))
    checkSameExpr(Times(toSum(lhs), toSum(rhs)), toSum(multiply(lhs, rhs)), xs)
    checkSameExpr(Times(toSum(rhs), toSum(lhs)), toSum(multiply(rhs, lhs)), xs)

    val lhs2 = Seq(x, y, i(2))
    val rhs2 = Seq(y, i(1), Times(i(2), x))
    checkSameExpr(Times(toSum(lhs2), toSum(rhs2)), toSum(multiply(lhs2, rhs2)), xs)
  }

  test("expandedForm") {
    val e1 = Times(Plus(x, i(2)), Plus(y, i(1)))
    checkSameExpr(toSum(expandedForm(e1)), e1, xs)

    val e2 = Times(Plus(x, Times(i(2), y)), Plus(Plus(x, y), i(1)))
    checkSameExpr(toSum(expandedForm(e2)), e2, xs)

    val e3 = Minus(Plus(x, Times(i(2), y)), Plus(Plus(x, y), i(1)))
    checkSameExpr(toSum(expandedForm(e3)), e3, xs)

    val e4 = UMinus(Plus(x, Times(i(2), y)))
    checkSameExpr(toSum(expandedForm(e4)), e4, xs)
  }

  test("linearArithmeticForm") {
    val xsOrder = Array(xId, yId)

    val e1 = Plus(Times(Plus(x, i(2)), i(3)), Times(i(4), y))
    checkSameExpr(coefToSum(linearArithmeticForm(e1, xsOrder), Array(x, y)), e1, xs)

    val e2 = Plus(Times(Plus(x, i(2)), i(3)), Plus(Plus(a, Times(i(5), b)), Times(i(4), y)))
    checkSameExpr(coefToSum(linearArithmeticForm(e2, xsOrder), Array(x, y)), e2, xs ++ as)

    val e3 = Minus(Plus(x, i(3)), Plus(y, i(2)))
    checkSameExpr(coefToSum(linearArithmeticForm(e3, xsOrder), Array(x, y)), e3, xs)

    val e4 = Plus(Plus(i(0), i(2)), Times(i(-1), i(3)))
    assert(linearArithmeticForm(e4, Array()) === Array(i(-1)))

  }
}
