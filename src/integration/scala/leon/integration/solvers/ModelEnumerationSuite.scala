/* Copyright 2009-2015 EPFL, Lausanne */

package leon.integration.solvers

import leon.integration.LeonTestSuiteWithProgram
import leon.integration.helpers.ExpressionsDSL
import leon.test._
import leon._
import leon.solvers._
import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.evaluators._
import leon.purescala.Expressions._

class ModelEnumeratorSuite extends LeonTestSuiteWithProgram with ExpressionsDSL {
  val sources = List(
    """|import leon.lang._
       |import leon.annotation._
       |
       |object List1 {
       |  abstract class List
       |  case class Cons(h: BigInt, t: List) extends List
       |  case object Nil extends List
       |
       |  def size(l: List): BigInt = {
       |    l match {
       |      case Cons(h, t) => BigInt(1) + size(t)
       |      case Nil => BigInt(0)
       |    }
       |  } ensuring { _ >= 0 }
       |
       |  def sum(l: List): BigInt = l match {
       |    case Cons(h, t) => h + size(t)
       |    case Nil => 0
       |  }
       |
       |  def sumAndSize(l: List) = (size(l), sum(l))
       |
       |} """.stripMargin
  )

  def getModelEnum(implicit ctx: LeonContext, pgm: Program) = {
    val sf = SolverFactory.default.asInstanceOf[SolverFactory[IncrementalSolver]]
    new ModelEnumerator(ctx, pgm, sf)
  }

  test("Simple model enumeration 1") { implicit fix =>
    val tpe = classDef("List1.List").typed
    val l   = FreshIdentifier("l", tpe)

    val cnstr = GreaterThan(fcall("List1.size")(l.toVariable), bi(2))

    val me = getModelEnum
    try {
      val models = me.enumSimple(Seq(l), cnstr).take(5).toList

      assert(models.size === 5, "We can enumerate at least 5 lists of size 3+")
      assert(models.toSet.size === 5, "Models are distinct")
    } finally {
      me.shutdown()
    }
  }

  test("Simple model enumeration 2") { implicit fix =>
    val tpe = classDef("List1.List").typed
    val l   = FreshIdentifier("l", tpe)

    val cnstr = Equals(fcall("List1.size")(l.toVariable), bi(0))

    val me = getModelEnum

    try {
      val models = me.enumSimple(Seq(l), cnstr).take(5).toList

      assert(models.size === 1, "We can only enumerate one list of size 0")
    } finally {
      me.shutdown()
    }
  }

  test("Varying model enumeration 1") { implicit fix =>
    val tpe = classDef("List1.List").typed
    val l   = FreshIdentifier("l", tpe)

    // 0 < list.size < 3
    val cnstr = And(GreaterThan(fcall("List1.size")(l.toVariable), bi(0)),
                    LessThan(fcall("List1.size")(l.toVariable), bi(3)))

    val car   = fcall("List1.size")(l.toVariable)

    val evaluator = new DefaultEvaluator(fix._1, fix._2)
    val me = getModelEnum

    try {
      // 1 model of each size
      val models1 = me.enumVarying(Seq(l), cnstr, car).toList
      assert(models1.size === 2, "We can enumerate 2 lists of varying size 0 < .. < 3")

      // 3 models of each size
      val models2 = me.enumVarying(Seq(l), cnstr, car, 3).toList
      assert(models2.size === 6, "We can enumerate 6 lists of varying size 0 < .. < 3 with 3 per size")


      val car2   = fcall("List1.sum")(l.toVariable)

      // 1 model of each sum
      val models3 = me.enumVarying(Seq(l), cnstr, car2).take(4).toList
      assert(models3.size === 4, "We can enumerate >=4 lists of varying sum, with 0 < .. < 3")

      val carResults3 = models3.groupBy(m => evaluator.eval(car2, m).result.get)
      assert(carResults3.size === 4, "We should have 4 distinct sums")
      assert(carResults3.forall(_._2.size === 1), "We should have 1 model per sum")

      // 2 model of each sum
      val models4 = me.enumVarying(Seq(l), cnstr, car2, 2).take(4).toList
      assert(models4.size === 4, "We can enumerate >=4 lists of varying sum, with 0 < .. < 3")

      val carResults4 = models4.groupBy(m => evaluator.eval(car2, m).result.get)
      assert(carResults4.size >= 2, "We should have at least 2 distinct sums")
      assert(carResults4.forall(_._2.size <= 2), "We should have at most 2 models per sum")


    } finally {
      me.shutdown()
    }
  }

  test("Varying model enumeration 2") { implicit fix =>
    val tpe = classDef("List1.List").typed
    val l   = FreshIdentifier("l", tpe)

    // 0 < list.size < 3
    val cnstr = And(GreaterThan(fcall("List1.size")(l.toVariable), bi(0)),
                    LessThan(fcall("List1.size")(l.toVariable), bi(3)))

    val car   = Equals(fcall("List1.size")(l.toVariable), bi(1))

    val me = getModelEnum

    try {
      // 1 model of each caracteristic (which is a boolean, so only two possibilities)
      val models3 = me.enumVarying(Seq(l), cnstr, car).take(10).toList
      assert(models3.size === 2, "We can enumerate only 2 lists of varying size==0")


      // 1 model of each caracteristic (which is a boolean, so only two possibilities)
      val models4 = me.enumVarying(Seq(l), cnstr, car, 2).take(10).toList
      assert(models4.size === 4, "We can enumerate only 4 lists of varying size==0 (2 each)")

    } finally {
      me.shutdown()
    }
  }

  test("Maximizing size") { implicit fix =>
    val tpe = classDef("List1.List").typed
    val l   = FreshIdentifier("l", tpe)

    val cnstr = LessThan(fcall("List1.size")(l.toVariable), bi(5))

    val car   = fcall("List1.size")(l.toVariable)

    val evaluator = new DefaultEvaluator(fix._1, fix._2)
    val me = getModelEnum

    try {
      val models1 = me.enumMaximizing(Seq(l), cnstr, car).take(5).toList

      assert(models1.size < 5, "It took less than 5 models to reach max")
      assert(evaluator.eval(car, models1.last).result === Some(bi(4)), "Max should be 4")

      val models2 = me.enumMaximizing(Seq(l), BooleanLiteral(true), car).take(4).toList

      assert(models2.size == 4, "Unbounded search yields models")
      // in 4 steps, it should reach lists of size > 10
      assert(evaluator.eval(GreaterThan(car, bi(10)), models2.last).result === Some(T), "Progression should be efficient")
    } finally {
      me.shutdown()
    }
  }

  test("Minimizing size") { implicit fix =>
    val tpe = classDef("List1.List").typed
    val l   = FreshIdentifier("l", tpe)

    val cnstr = LessThan(fcall("List1.size")(l.toVariable), bi(5))

    val car   = fcall("List1.size")(l.toVariable)

    val evaluator = new DefaultEvaluator(fix._1, fix._2)
    val me = getModelEnum

    try {
      val models1 = me.enumMinimizing(Seq(l), cnstr, car).take(5).toList

      assert(models1.size < 5, "It took less than 5 models to reach min")
      assert(evaluator.eval(car, models1.last).result === Some(bi(0)), "Min should be 0")

    } finally {
      me.shutdown()
    }
  }

}
