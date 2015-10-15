/* Copyright 2009-2015 EPFL, Lausanne */

package leon.unit.orb

import leon.test._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.Common._
import leon.purescala.ExprOps._
import leon.invariant.util.LetTupleSimplification
import scala.math.BigInt.int2bigInt

class SimplifyLetsSuite extends LeonTestSuite {
  val a = FreshIdentifier("a", IntegerType)
  val b = FreshIdentifier("b", IntegerType)
  val c = FreshIdentifier("c", IntegerType)
  val l42 = InfiniteIntegerLiteral(42)
  val l43 = InfiniteIntegerLiteral(43)

  test("Pull lets to top with tuples and tuple select") { ctx =>
    val in  = TupleSelect(Tuple(Seq(a.toVariable, b.toVariable)), 1)
    val exp = in
    val out = LetTupleSimplification.removeLetsFromLetValues(in)
    assert(out === exp)
  }
}
