/* Copyright 2009-2015 EPFL, Lausanne */

package leon.unit.purescala

import leon.test._
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Definitions._
import leon.purescala.Types._
import leon.purescala.ExprOps._
import leon.purescala.TypeOps._

class TypeOpsSuite extends LeonTestSuite with helpers.WithLikelyEq with helpers.ExpressionsDSL {

  test("canBeSubtypeOf 1") { ctx =>
    val tp    = TypeParameter.fresh("T")
    val tpD   = new TypeParameterDef(tp)

    val tp2   = TypeParameter.fresh("A")
    val tp3   = TypeParameter.fresh("B")

    val listD = AbstractClassDef(FreshIdentifier("List"), Seq(tpD), None)
    val listT = listD.typed

    val nilD  = CaseClassDef(FreshIdentifier("Nil"),  Seq(tpD), Some(listT), false)
    val nilT  = nilD.typed

    val consD = CaseClassDef(FreshIdentifier("Cons"), Seq(tpD), Some(listT), false)
    val consT = consD.typed

    // Simple tests for fixed types
    assert(canBeSubtypeOf(tp,       Seq(), tp).isDefined,    "Same types can be subtypes")
    assert(canBeSubtypeOf(listT,    Seq(), listT).isDefined, "Different types are not subtypes")

    assert(canBeSubtypeOf(tp2,          Seq(), tp3).isEmpty,         "Different types are not subtypes")
    assert(canBeSubtypeOf(BooleanType,  Seq(), tp3).isEmpty,         "Different types are not subtypes")
    assert(canBeSubtypeOf(tp2,          Seq(), BooleanType).isEmpty, "Different types are not subtypes")
    assert(canBeSubtypeOf(IntegerType,  Seq(), Int32Type).isEmpty,   "Different types are not subtypes")

    assert(canBeSubtypeOf(nilT,         Seq(), listT).isDefined,   "Subtypes are subtypes")
    assert(canBeSubtypeOf(consT,        Seq(), listT).isDefined,   "Subtypes are subtypes")

    assert(canBeSubtypeOf(listT,        Seq(), nilT).isEmpty,    "Supertypes are not subtypes")
    assert(canBeSubtypeOf(listT,        Seq(), consT).isEmpty,   "Supertypes are not subtypes")

    // Type parameters
    assert(canBeSubtypeOf(tp,           Seq(tp),  tp2).isDefined,    "T <: A with T free")
    assert(canBeSubtypeOf(tp,           Seq(tp2), tp2).isDefined,    "T <: A with A free")

    assert(canBeSubtypeOf(listT,        Seq(tp),  listD.typed(Seq(tp2))).isDefined,    "List[T] <: List[A] with T free")
    assert(canBeSubtypeOf(listT,        Seq(tp2), listD.typed(Seq(tp2))).isDefined,    "List[T] <: List[A] with A free")

    // Type parameters with fixed sides
    assert(canBeSubtypeOf(tp,           Seq(tp),  tp2, lhsFixed = true).isEmpty,    "T </: A with T free when lhs is fixed")
    assert(canBeSubtypeOf(tp,           Seq(tp),  tp2, rhsFixed = true).isDefined,  "T <: A with T free but rhs is fixed")
    assert(canBeSubtypeOf(tp,           Seq(tp2), tp2, lhsFixed = true).isDefined,  "T <: A with A free when lhs is fixed")
    assert(canBeSubtypeOf(tp,           Seq(tp2), tp2, rhsFixed = true).isEmpty,    "T </: A with A free but lhs is fixed")

    assert(canBeSubtypeOf(listT,        Seq(tp),  listD.typed(Seq(tp2)), rhsFixed = true).isDefined,    "List[T] <: List[A] with T free and rhs fixed")

    assert(isSubtypeOf(listD.typed, listD.typed), "List[T] <: List[T]")
  }

  test("instantiateType Hole") { ctx =>
    val tp1 = TypeParameter.fresh("a")
    val tp2 = TypeParameter.fresh("b")

    val tpd = TypeParameterDef(tp1)

    val e1 = Hole(tp1, Nil)
    val e2 = instantiateType(e1, Map(tpd -> tp2), Map())

    e2 match {
      case Hole(tp, _) => assert(tp == tp2, "Type should have been substituted")
      case _ => fail("Incorrect expr shape, should be a Hole")
    }
  }

}
