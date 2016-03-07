/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.purescala

import leon.test._

import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Types._
import leon.purescala.Expressions._
import leon.purescala.TreeNormalizations._

class TreeNormalizationsSuite extends LeonTestSuite with helpers.WithLikelyEq with helpers.ExpressionsDSL {

  def toSum(es: Seq[Expr]) = es.reduceLeft(Plus)
  def coefToSum(es: Array[Expr], vs: Array[Expr]) = es.zip(Array[Expr](InfiniteIntegerLiteral(1)) ++ vs).foldLeft[Expr](InfiniteIntegerLiteral(0))((acc, p) => Plus(acc, Times(p._1, p._2)))
  
  test("checkSameExpr") { ctx =>
    checkLikelyEq(ctx)(Plus(x, y), Plus(y, x))
    checkLikelyEq(ctx)(Plus(x, x), Times(x, bi(2)))
    checkLikelyEq(ctx)(Plus(x, Plus(x, x)), Times(x, bi(3)))
  }

  test("multiply") { ctx =>
    val lhs = Seq(x, bi(2))
    val rhs = Seq(y, bi(1))
    checkLikelyEq(ctx)(Times(toSum(lhs), toSum(rhs)), toSum(multiply(lhs, rhs)))
    checkLikelyEq(ctx)(Times(toSum(rhs), toSum(lhs)), toSum(multiply(rhs, lhs)))

    val lhs2 = Seq(x, y, bi(2))
    val rhs2 = Seq(y, bi(1), Times(bi(2), x))
    checkLikelyEq(ctx)(Times(toSum(lhs2), toSum(rhs2)), toSum(multiply(lhs2, rhs2)))
  }

  test("expandedForm") { ctx =>
    val e1 = Times(Plus(x, bi(2)), Plus(y, bi(1)))
    checkLikelyEq(ctx)(toSum(expandedForm(e1)), e1)

    val e2 = Times(Plus(x, Times(bi(2), y)), Plus(Plus(x, y), bi(1)))
    checkLikelyEq(ctx)(toSum(expandedForm(e2)), e2)

    val e3 = Minus(Plus(x, Times(bi(2), y)), Plus(Plus(x, y), bi(1)))
    checkLikelyEq(ctx)(toSum(expandedForm(e3)), e3)

    val e4 = UMinus(Plus(x, Times(bi(2), y)))
    checkLikelyEq(ctx)(toSum(expandedForm(e4)), e4)
  }

  test("linearArithmeticForm") { ctx =>
    val xsOrder = Array(x.id, y.id)

    val aa = FreshIdentifier("aa", IntegerType).toVariable
    val bb = FreshIdentifier("bb", IntegerType).toVariable

    val e1 = Plus(Times(Plus(x, bi(2)), bi(3)), Times(bi(4), y))
    checkLikelyEq(ctx)(coefToSum(linearArithmeticForm(e1, xsOrder), Array(x, y)), e1)

    val e2 = Plus(Times(Plus(x, bi(2)), bi(3)), Plus(Plus(aa, Times(bi(5), bb)), Times(bi(4), y)))
    checkLikelyEq(ctx)(coefToSum(linearArithmeticForm(e2, xsOrder), Array(x, y)), e2)

    val e3 = Minus(Plus(x, bi(3)), Plus(y, bi(2)))
    checkLikelyEq(ctx)(coefToSum(linearArithmeticForm(e3, xsOrder), Array(x, y)), e3)

    val e4 = Plus(Plus(bi(0), bi(2)), Times(bi(-1), bi(3)))
    assert(linearArithmeticForm(e4, Array()) === Array(bi(-1)))

  }
}
