package leon.test.synthesis

import org.scalatest.FunSuite

import leon.Evaluator
import leon.purescala.Trees._
import leon.purescala.Common._

import leon.synthesis.ArithmeticNormalization._

class ArithmeticNormalizationSuite extends FunSuite {

  def i(x: Int) = IntLiteral(x)

  val xId = FreshIdentifier("x")
  val x = Variable(xId)
  val yId = FreshIdentifier("y")
  val y = Variable(yId)

  val aId = FreshIdentifier("a")
  val a = Variable(aId)
  val bId = FreshIdentifier("b")
  val b = Variable(bId)
  
  val allMaps: Seq[Map[Identifier, Expr]] = (-20 to 20).flatMap(xVal => (-20 to 20).map(yVal => Map(xId-> i(xVal), yId -> i(yVal))))

  def checkSameExpr(e1: Expr, e2: Expr) {
    allMaps.foreach(m =>
      assert(Evaluator.eval(m, e1, None) === Evaluator.eval(m, e2, None))
    )
  }

  def toSum(es: Seq[Expr]) = es.reduceLeft(Plus(_, _))
  
  test("checkSameExpr") {
    checkSameExpr(Plus(x, y), Plus(y, x))
    checkSameExpr(Plus(x, x), Times(x, i(2)))
    checkSameExpr(Plus(x, Plus(x, x)), Times(x, i(3)))
  }

  test("multiply") {
    val lhs = Seq(x, i(2))
    val rhs = Seq(y, i(1))
    checkSameExpr(Times(toSum(lhs), toSum(rhs)), toSum(multiply(lhs, rhs)))
    checkSameExpr(Times(toSum(rhs), toSum(lhs)), toSum(multiply(rhs, lhs)))

    val lhs2 = Seq(x, y, i(2))
    val rhs2 = Seq(y, i(1), Times(i(2), x))
    checkSameExpr(Times(toSum(lhs2), toSum(rhs2)), toSum(multiply(lhs2, rhs2)))
  }

  test("expand") {
    val e1 = Times(Plus(x, i(2)), Plus(y, i(1)))
    checkSameExpr(toSum(expand(e1)), e1)

    val e2 = Times(Plus(x, Times(i(2), y)), Plus(Plus(x, y), i(1)))
    checkSameExpr(toSum(expand(e2)), e2)

  }

  test("apply") {
    val xs = Array(xId, yId)

    val e1 = Plus(Times(Plus(x, i(2)), i(3)), Times(i(4), y))
    checkSameExpr(toSum(apply(e1, xs)), e1)

    val e2 = Plus(Times(Plus(x, i(2)), i(3)), Plus(Plus(a, Times(i(5), b)), Times(i(4), y)))
    checkSameExpr(toSum(apply(e2, xs)), e2)

  }
  

}
