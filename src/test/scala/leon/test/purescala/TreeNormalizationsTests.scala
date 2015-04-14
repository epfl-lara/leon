/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.purescala

import leon.test._

import leon.purescala.Common._
import leon.purescala.Types._
import leon.purescala.Expressions._
import leon.purescala.TreeNormalizations._

class TreeNormalizationsTests extends LeonTestSuite with WithLikelyEq {
  def i(x: Int) = InfiniteIntegerLiteral(x)

  val xId = FreshIdentifier("x", IntegerType)
  val x = Variable(xId)
  val yId = FreshIdentifier("y", IntegerType)
  val y = Variable(yId)
  val xs = Set(xId, yId)

  val aId = FreshIdentifier("a", IntegerType)
  val a = Variable(aId)
  val bId = FreshIdentifier("b", IntegerType)
  val b = Variable(bId)
  val as = Set(aId, bId)
  

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
