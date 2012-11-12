package leon.test.synthesis

import org.scalatest.FunSuite

import leon.Evaluator
import leon.purescala.Trees._
import leon.purescala.Common._

import leon.synthesis.ArithmeticNormalization._
import leon.synthesis.LikelyEq

class ArithmeticNormalizationSuite extends FunSuite {

  def i(x: Int) = IntLiteral(x)

  val xId = FreshIdentifier("x")
  val x = Variable(xId)
  val yId = FreshIdentifier("y")
  val y = Variable(yId)
  val xs = Set(xId, yId)

  val aId = FreshIdentifier("a")
  val a = Variable(aId)
  val bId = FreshIdentifier("b")
  val b = Variable(bId)
  val as = Set(aId, bId)
  
  val allMaps: Seq[Map[Identifier, Expr]] = (-20 to 20).flatMap(xVal => (-20 to 20).map(yVal => Map(xId-> i(xVal), yId -> i(yVal))))

  def checkSameExpr(e1: Expr, e2: Expr, vs: Set[Identifier]) {
    assert( //this outer assert should not be needed because of the nested one
      LikelyEq(e1, e2, vs, BooleanLiteral(true), (e1, e2) => {assert(e1 === e2); true})
    )
  }

  def toSum(es: Seq[Expr]) = es.reduceLeft(Plus(_, _))
  def coefToSum(es: Array[Expr], vs: Array[Expr]) = (es.zip(Array[Expr](IntLiteral(1)) ++ vs)).foldLeft[Expr](IntLiteral(0))((acc, p) => Plus(acc, Times(p._1, p._2)))
  
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

  test("expand") {
    val e1 = Times(Plus(x, i(2)), Plus(y, i(1)))
    checkSameExpr(toSum(expand(e1)), e1, xs)

    val e2 = Times(Plus(x, Times(i(2), y)), Plus(Plus(x, y), i(1)))
    checkSameExpr(toSum(expand(e2)), e2, xs)

  }

  test("apply") {
    val xsOrder = Array(xId, yId)

    val e1 = Plus(Times(Plus(x, i(2)), i(3)), Times(i(4), y))
    checkSameExpr(coefToSum(apply(e1, xsOrder), Array(x, y)), e1, xs)

    val e2 = Plus(Times(Plus(x, i(2)), i(3)), Plus(Plus(a, Times(i(5), b)), Times(i(4), y)))
    checkSameExpr(coefToSum(apply(e2, xsOrder), Array(x, y)), e2, xs ++ as)

  }


  test("simplify") {
    val e1 = Plus(IntLiteral(3), IntLiteral(2))
    checkSameExpr(e1, simplify(e1), Set())
    val e2 = Plus(x, Plus(IntLiteral(3), IntLiteral(2)))
    checkSameExpr(e2, simplify(e2), Set(xId))

    val e3 = Minus(IntLiteral(3), IntLiteral(2))
    checkSameExpr(e3, simplify(e3), Set())
    val e4 = Plus(x, Minus(IntLiteral(3), IntLiteral(2)))
    checkSameExpr(e4, simplify(e4), Set(xId))
    val e5 = Plus(x, Minus(x, IntLiteral(2)))
    checkSameExpr(e5, simplify(e5), Set(xId))
  }


  test("extractEquals") {
    val eq = Equals(a, b)
    val lt1 = LessThan(a, b)
    val lt2 = LessThan(b, a)
    val lt3 = LessThan(x, y)

    val f1 = And(Seq(eq, lt1, lt2, lt3))
    val (eq1, r1) = extractEquals(f1)
    assert(eq1 != None)
    assert(eq1.get === eq)
    assert(extractEquals(r1)._1 === None)

    val f2 = And(Seq(lt1, lt2, eq, lt3))
    val (eq2, r2) = extractEquals(f2)
    assert(eq2 != None)
    assert(eq2.get === eq)
    assert(extractEquals(r2)._1 === None)

    val f3 = And(Seq(lt1, eq, lt2, lt3, eq))
    val (eq3, r3) = extractEquals(f3)
    assert(eq3 != None)
    assert(eq3.get === eq)
    val (eq4, r4) = extractEquals(r3)
    assert(eq4 != None)
    assert(eq4.get === eq)
    assert(extractEquals(r4)._1 === None)

  }
  
}
