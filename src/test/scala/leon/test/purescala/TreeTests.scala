/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package purescala

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._

class TreeTests extends LeonTestSuite {

  test("And- and Or- simplifications") {
    val x = Variable(FreshIdentifier("x").setType(BooleanType))
    val t = BooleanLiteral(true)
    val f = BooleanLiteral(false)

    def and(es : Expr*) : Expr = And(Seq(es : _*))
    def or(es : Expr*) : Expr = Or(Seq(es : _*))

    assert(and(x, and(x, x), x) === and(x, x, x, x))
    assert(and(x, t, x, t) === and(x, x))
    assert(and(x, t, f, x) === and(x, f))
    assert(and(x) === x)
    assert(and() === t)
    assert(and(t, t) === t)
    assert(and(f) === f)

    assert(or(x, or(x, x), x) === or(x, x, x, x))
    assert(or(x, f, x, f) === or(x, x))
    assert(or(x, f, t, x) === or(x, t))
    assert(or(x) === x)
    assert(or() === f)
    assert(or(f, f) === f)
    assert(or(t) === t)
  }
}
