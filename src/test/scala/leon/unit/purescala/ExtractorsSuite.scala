/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.xlang

import org.scalatest._

import leon.test.helpers.ExpressionsDSL
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Extractors._

class ExtractorsSuite extends FunSuite with ExpressionsDSL {

  test("Extractors do not simplify basic arithmetic") {
    val e1 = BVPlus(1, 1)
    val e2 = e1 match {
      case Operator(es, builder) => builder(es)
    }
    assert(e1 === e2)

    val e3 = Times(x, BigInt(1))
    val e4 = e3 match {
      case Operator(es, builder) => builder(es)
    }
    assert(e3 === e4)
  }

  ignore("Extractors of NonemptyArray with sparse elements") {
    val a1 = NonemptyArray(Map(0 -> x, 3 -> y, 5 -> z), Some((BigInt(0), BigInt(10))))

    val a2 = a1 match {
      case Operator(es, builder) => {
        assert(es === Seq(x, y, z, InfiniteIntegerLiteral(0), InfiniteIntegerLiteral(10)))
        builder(es)
      }
    }

    assert(a2 === a1)
  }

}
