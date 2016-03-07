/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.purescala

import leon.test._

import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.Common._
import leon.purescala.ExprOps._

class SimplifyLetsSuite extends LeonTestSuite {
  val a = FreshIdentifier("a", IntegerType)
  val b = FreshIdentifier("b", IntegerType)
  val c = FreshIdentifier("c", IntegerType)
  val l42 = InfiniteIntegerLiteral(42)
  val l43 = InfiniteIntegerLiteral(43)

  test("Simplify Lets 01 - double use of simple let") { ctx => 
    val in  = Let(b, l42, Plus(a.toVariable, Plus(b.toVariable, b.toVariable)))
    val exp = Plus(a.toVariable, Plus(l42, l42))

    val out = simplifyLets(in)
    assert(out === exp)
  }

  test("Simplify Lets 02 - single use of expr let") { ctx => 
    val in  = Let(b, Plus(l42, a.toVariable), Plus(a.toVariable, b.toVariable))
    val exp = Plus(a.toVariable, Plus(l42, a.toVariable))

    val out = simplifyLets(in)
    assert(out === exp)
  }

  test("Simplify Lets 03 - unused let") { ctx => 
    val in  = Let(b, l42,
              Let(c, l43,
                Plus(a.toVariable, c.toVariable)))

    val exp = Plus(a.toVariable, l43)

    val out = simplifyLets(in)
    assert(out === exp)
  }

  test("Simplify Lets 04 - double use of expr let") { ctx => 
    val in  = Let(b, Plus(l42, a.toVariable), Plus(a.toVariable, Plus(b.toVariable, b.toVariable)))
    val exp = in

    val out = simplifyLets(in)
    assert(out === exp)
  }

}
