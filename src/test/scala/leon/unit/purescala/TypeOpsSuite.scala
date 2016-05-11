/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.purescala

import leon.test._
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Definitions._
import leon.purescala.Types._
import leon.purescala.TypeOps._

class TypeOpsSuite extends LeonTestSuite with helpers.WithLikelyEq with helpers.ExpressionsDSL {

  test("type bounds") { ctx =>
    val tp    = TypeParameter.fresh("T")
    val tpD   = new TypeParameterDef(tp)

    val tp2   = TypeParameter.fresh("A")
    val tp3   = TypeParameter.fresh("B")

    val listD = new AbstractClassDef(FreshIdentifier("List"), Seq(tpD), None)
    val listT = listD.typed

    val nilD  = new CaseClassDef(FreshIdentifier("Nil"),  Seq(tpD), Some(listT), false)
    val nilT  = nilD.typed

    val consD = new CaseClassDef(FreshIdentifier("Cons"), Seq(tpD), Some(listT), false)
    val consT = consD.typed

    assert(isSubtypeOf(tp,    tp),                "T <: T")
    assert(isSubtypeOf(listT, listT),             "List[T] <: List[T]")
    assert(isSubtypeOf(listD.typed, listD.typed), "List[T] <: List[T]")

    assert(isSubtypeOf(nilT,  listT), "Subtypes are subtypes")
    assert(isSubtypeOf(consT, listT), "Subtypes are subtypes")

    assert(!isSubtypeOf(listT, nilT ), "Supertypes are not subtypes")
    assert(!isSubtypeOf(listT, consT), "Supertypes are not subtypes")

    assert(!isSubtypeOf(nilD.typed(Seq(tp2)), listD.typed(Seq(tp3))),         "Types are not subtypes with incompatible params")
    assert(!isSubtypeOf(nilD.typed(Seq(tp2)), listD.typed(Seq(IntegerType))), "Types are not subtypes with incompatible params")
    assert(!isSubtypeOf(SetType(tp2),         SetType(tp3)),                  "Types are not subtypes with incompatible params")

    assert(!isSubtypeOf(nilD.typed(Seq(nilT)), listD.typed(Seq(listT))), "Classes are invariant")
    assert(!isSubtypeOf(SetType(nilT),         SetType(listT)),          "Sets are invariant")

    assert(isSubtypeOf(FunctionType(Seq(listT), nilT), FunctionType(Seq(nilT), listT)), "Functions have contravariant params/ covariant result")

    assert(!typesCompatible(tp2,         tp3),          "Different types should be incompatible")
    assert(!typesCompatible(BooleanType, tp3),          "Different types should be incompatible")
    assert(!typesCompatible(tp2,         BooleanType),  "Different types should be incompatible")
    assert(!typesCompatible(IntegerType, Int32Type),    "Different types should be incompatible")

    // Type parameters
    assert(unify(tp, tp2, Seq(tp) ).isDefined, "T <: A with T free")
    assert(unify(tp, tp2, Seq(tp2)).isDefined, "T <: A with A free")

    assert(unify(listT, listD.typed(Seq(tp2)), Seq(tp) ).isDefined, "List[T] <: List[A] with T free")
    assert(unify(listT, listD.typed(Seq(tp2)), Seq(tp2)).isDefined, "List[T] <: List[A] with A free")
    assert(unify(listT, listD.typed(Seq(tp2)), Seq()   ).isEmpty,   "List[T] !<: List[A] with A,T not free")
    assert(unify(listT, nilT,                  Seq(tp) ).isEmpty,   "Subtypes not unifiable")

    assert(
      unify(MapType(IntegerType, tp), MapType(tp2, IntegerType), Seq(tp, tp2)).contains(Map(tp -> IntegerType, tp2 -> IntegerType)),
      "MapType unifiable"
    )

    assert(
      subtypingInstantiation(consD.typed(Seq(tp)), listD.typed(Seq(tp2))) contains Map(tp2 -> tp),
      "Cons[T] <: List[A] under A -> T"
    )

    assert(
      subtypingInstantiation(consD.typed(Seq(IntegerType)), listD.typed(Seq(tp2))) contains Map(tp2 -> IntegerType),
      "Cons[BigInt] <: List[A] under A -> BigInt"
    )

    assert(
      subtypingInstantiation(consD.typed(Seq(tp)), listD.typed(Seq(IntegerType))).isEmpty,
      "List[BigInt] cannot be instantiated such that Cons[T] <: List[BigInt]"
    )
  }

  test("instantiateType Hole") { ctx =>
    val tp1 = TypeParameter.fresh("a")
    val tp2 = TypeParameter.fresh("b")

    val e1 = Hole(tp1, Nil)
    val e2 = instantiateType(e1, Map(tp1 -> tp2), Map())

    e2 match {
      case Hole(tp, _) => assert(tp == tp2, "Type should have been substituted")
      case _ => fail("Incorrect expr shape, should be a Hole")
    }
  }

}
