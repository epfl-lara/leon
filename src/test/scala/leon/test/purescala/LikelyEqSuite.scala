/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test.purescala

import org.scalatest.FunSuite

import leon.purescala.Common._
import leon.purescala.Trees._


class LikelyEqSuite extends FunSuite {
  def i(x: Int) = IntLiteral(x)

  val xId = FreshIdentifier("x")
  val x = Variable(xId)
  val yId = FreshIdentifier("y")
  val y = Variable(yId)
  val zId = FreshIdentifier("z")
  val z = Variable(zId)

  test("apply") {
    assert(LikelyEq(Plus(x, x), Times(IntLiteral(2), x), Set(xId)))
    assert(LikelyEq(Plus(x, x), Times(x, IntLiteral(2)), Set(xId)))

    assert(LikelyEq(Plus(x, y), Plus(y, x), Set(xId, yId)))
    assert(LikelyEq(Plus(Plus(x, y), y), Plus(x, Times(IntLiteral(2), y)), Set(xId, yId)))

    def defaultCompare(e1: Expr, e2: Expr) = e1 == e2

    assert(LikelyEq(
      Plus(IntLiteral(2), Plus(x, y)), 
      Plus(IntLiteral(3), Plus(x, z)), 
      Set(xId), 
      BooleanLiteral(true),
      defaultCompare, 
      Map(yId -> IntLiteral(2), zId -> IntLiteral(1)))
    )


    assert(LikelyEq(
      Plus(x, Times(IntLiteral(2), Division(y, IntLiteral(2))))
      , Plus(x, y)
      , Set(xId, yId)
      , Equals(Modulo(y, IntLiteral(2)), IntLiteral(0))
    ))

  }
  
}
