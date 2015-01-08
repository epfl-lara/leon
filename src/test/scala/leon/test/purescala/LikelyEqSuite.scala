/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.purescala

import leon._
import leon.test._
import leon.purescala.Common._
import leon.purescala.Trees._


class LikelyEqSuite extends LeonTestSuite with WithLikelyEq {
  def i(x: Int) = InfiniteIntegerLiteral(x)

  val xId = FreshIdentifier("x")
  val x = Variable(xId)
  val yId = FreshIdentifier("y")
  val y = Variable(yId)
  val zId = FreshIdentifier("z")
  val z = Variable(zId)

  test("apply") {
    assert(LikelyEq(Plus(x, x), Times(i(2), x), Set(xId)))
    assert(LikelyEq(Plus(x, x), Times(x, i(2)), Set(xId)))

    assert(LikelyEq(Plus(x, y), Plus(y, x), Set(xId, yId)))
    assert(LikelyEq(Plus(Plus(x, y), y), Plus(x, Times(i(2), y)), Set(xId, yId)))

    def defaultCompare(e1: Expr, e2: Expr) = e1 == e2

    assert(LikelyEq(
      Plus(i(2), Plus(x, y)), 
      Plus(i(3), Plus(x, z)), 
      Set(xId), 
      BooleanLiteral(true),
      defaultCompare, 
      Map(yId -> i(2), zId -> i(1)))
    )


    assert(LikelyEq(
      Plus(x, Times(i(2), Division(y, i(2))))
      , Plus(x, y)
      , Set(xId, yId)
      , Equals(Modulo(y, i(2)), i(0))
    ))

  }
  
}
