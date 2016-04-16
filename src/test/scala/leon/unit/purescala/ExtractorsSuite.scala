/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.purescala

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

  test("Extractors do not magically change the syntax") {
    val e1 = Equals(bi(1), bi(1))
    val e2 = e1 match {
      case Operator(es, builder) => builder(es)
    }
    assert(e1 === e2)

    val e3 = Equals(BooleanLiteral(true), BooleanLiteral(false))
    val e4 = e3 match {
      case Operator(es, builder) => builder(es)
    }
    assert(e3 === e4)

    val e5 = TupleSelect(Tuple(Seq(bi(1), bi(2))), 2)
    val e6 = e5 match {
      case Operator(es, builder) => builder(es)
    }
    assert(e5 === e6)
  }


  test("Extractors of NonemptyArray with sparse elements") {
    val a1 = NonemptyArray(Map(0 -> x, 3 -> y, 5 -> z), Some((BigInt(0), BigInt(10))))
    val a2 = a1 match {
      case Operator(es, builder) => {
        assert(es === Seq(x, y, z, InfiniteIntegerLiteral(0), InfiniteIntegerLiteral(10)))
        builder(es)
      }
    }
    assert(a2 === a1)

    val a3 = NonemptyArray(Map(0 -> x, 1 -> y, 2 -> z), None)
    val a4 = a3 match {
      case Operator(es, builder) => {
        assert(es === Seq(x, y, z))
        builder(es)
      }
    }
    assert(a3 === a4)
  }

}
