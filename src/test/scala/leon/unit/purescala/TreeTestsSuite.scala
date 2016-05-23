/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.purescala

import leon.test._

import leon.purescala.Common._
import leon.purescala.Constructors._
import leon.purescala.Expressions._
import leon.purescala.Types._

class TreeTestsSuite extends LeonTestSuite {

  test("And- and Or- simplifications") { ctx =>
    val x = FreshIdentifier("x", BooleanType).toVariable
    val t = BooleanLiteral(true)
    val f = BooleanLiteral(false)

    def and(es : Expr*) : Expr = andJoin(es)
    def or(es : Expr*) : Expr = orJoin(es)

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
