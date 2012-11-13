package leon.test.synthesis

import org.scalatest.FunSuite

import leon.Evaluator
import leon.purescala.Trees._
import leon.purescala.Common._

import leon.synthesis.ArithmeticNormalization._
import leon.synthesis.LikelyEq
import leon.synthesis.IntegerSynthesis.apply

class IntegerSynthesisSuite extends FunSuite {

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
  
  test("apply") {

    val f1 = And(
      Equals(Plus(x, IntLiteral(2)), Plus(y, IntLiteral(3))),
      Equals(Minus(x, IntLiteral(1)), Plus(y, IntLiteral(2)))
    )

    //apply(as, xs, f1)
  }
  
}
