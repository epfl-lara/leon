/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.purescala

import leon.test._

import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.datagen._

import leon.evaluators._

class DataGenSuite extends LeonTestSuiteWithProgram with helpers.ExpressionsDSL {
  val sources = List(
    """|import leon.lang._
       |object Program {
       |  sealed abstract class List
       |  case class Cons(head: Int, tail: List) extends List
       |  case object Nil extends List
       |
       |  def size(lst: List): BigInt = lst match {
       |    case Cons(_, xs) => 1 + size(xs)
       |    case Nil => BigInt(0)
       |  }
       |
       |  def isSorted(lst: List) : Boolean = lst match {
       |    case Nil => true
       |    case Cons(_, Nil) => true
       |    case Cons(x, xs @ Cons(y, ys)) => x < y && isSorted(xs)
       |  }
       |
       |  def content(lst: List) : Set[Int] = lst match {
       |    case Nil => Set.empty[Int]
       |    case Cons(x, xs) => Set(x) ++ content(xs)
       |  }
       |
       |  def insertSpec(elem: Int, list: List, res: List) : Boolean = {
       |    isSorted(res) && content(res) == (content(list) ++ Set(elem))
       |  }
       |}""".stripMargin
  )

  test("Lists") { implicit fix =>

    val ctx = fix._1
    val pgm = fix._2

    val eval      = new DefaultEvaluator(ctx, pgm)
    val generator = new GrammarDataGen(eval)

    generator.generate(BooleanType).toSet.size === 2
    generator.generate(TupleType(Seq(BooleanType,BooleanType))).toSet.size === 4

    // Make sure we target our own lists

    val listType = classDef("Program.List").typed(Seq())

    assert(generator.generate(listType).take(100).toSet.size === 100, "Should be able to generate 100 different lists")

    val l1 = FreshIdentifier("l1", listType).toVariable
    val l2 = FreshIdentifier("l2", listType).toVariable

    def size(x: Expr)    = fcall("Program.size")(x)
    def content(x: Expr) = fcall("Program.content")(x)
    def sorted(x: Expr)  = fcall("Program.isSorted")(x)

    def spec(elem: Expr, list: Expr, res: Expr) = fcall("Program.insertSpec")(elem, list, res)
    def cons(h: Expr, t: Expr) = cc("Program.Cons")(h, t)

    assert(generator.generateFor(
      Seq(l1.id),
      GreaterThan(size(l1), bi(0)),
      10,
      500
    ).size === 10, "Should find 10 non-empty lists in the first 500 enumerated")

    assert(generator.generateFor(
      Seq(l1.id, l2.id),
      And(Equals(content(l1), content(l2)), sorted(l2)),
      10,
      500
    ).size === 10, "Should find 2x 10 lists with same content in the first 500 enumerated")

    assert(generator.generateFor(
      Seq(l1.id, l2.id),
      And(Seq(Equals(content(l1), content(l2)), sorted(l1), sorted(l2), Not(Equals(l1, l2)))),
      1,
      500
    ).isEmpty, "There should be no models for this problem")

    assert(generator.generateFor(
      Seq(l1.id, l2.id, b.id, a.id),
      And(Seq(
        LessThan(a, b),
        sorted(cons(a, l1)),
        spec(b, l1, l2)
      )),
      10,
      500
    ).size >= 5, "There should be at least 5 models for this problem.")
  }
}
