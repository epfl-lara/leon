/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.evaluators

import leon._
import leon.evaluators._ 

import leon.utils.{TemporaryInputPhase, PreprocessingPhase}
import leon.frontends.scalac.ExtractionPhase

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.DefOps._
import leon.purescala.TypeTrees._


class DefaultEvaluatorTests extends leon.test.LeonTestSuite {
  private implicit lazy val leonContext: LeonContext = createLeonContext()
  private val emptyProgram = Program.empty

  private val defaultEvaluator = new DefaultEvaluator(leonContext, emptyProgram)

  def expectSuccessful(res: EvaluationResults.Result, expected: Expr): Unit = {
    res match {
      case EvaluationResults.Successful(value) => assert(value === expected)
      case _ => assert(false)
    }
  }

  test("eval correctly evaluates literals") {
    expectSuccessful(defaultEvaluator.eval(BooleanLiteral(true)), BooleanLiteral(true))
    expectSuccessful(defaultEvaluator.eval(BooleanLiteral(false)), BooleanLiteral(false))
    expectSuccessful(defaultEvaluator.eval(IntLiteral(0)), IntLiteral(0))
    expectSuccessful(defaultEvaluator.eval(IntLiteral(42)), IntLiteral(42))
    expectSuccessful(defaultEvaluator.eval(UnitLiteral()), UnitLiteral())
  }

  test("eval of simple arithmetic expressions") {
    expectSuccessful(
      defaultEvaluator.eval(Plus(IntLiteral(3), IntLiteral(5))), IntLiteral(8))
    expectSuccessful(
      defaultEvaluator.eval(Minus(IntLiteral(7), IntLiteral(2))), IntLiteral(5))
    expectSuccessful(
      defaultEvaluator.eval(UMinus(IntLiteral(7))), IntLiteral(-7))
    expectSuccessful(
      defaultEvaluator.eval(Times(IntLiteral(2), IntLiteral(3))), IntLiteral(6)) 
    expectSuccessful(
      defaultEvaluator.eval(Modulo(IntLiteral(10), IntLiteral(3))), IntLiteral(1))
  }

  test("Eval of simple boolean operations") {
    expectSuccessful(
      defaultEvaluator.eval(And(BooleanLiteral(true), BooleanLiteral(true))),
      BooleanLiteral(true))
    expectSuccessful(
      defaultEvaluator.eval(And(BooleanLiteral(true), BooleanLiteral(false))),
      BooleanLiteral(false))
    expectSuccessful(
      defaultEvaluator.eval(And(BooleanLiteral(false), BooleanLiteral(false))),
      BooleanLiteral(false))
    expectSuccessful(
      defaultEvaluator.eval(And(BooleanLiteral(false), BooleanLiteral(true))),
      BooleanLiteral(false))
    expectSuccessful(
      defaultEvaluator.eval(Or(BooleanLiteral(true), BooleanLiteral(true))),
      BooleanLiteral(true))
    expectSuccessful(
      defaultEvaluator.eval(Or(BooleanLiteral(true), BooleanLiteral(false))),
      BooleanLiteral(true))
    expectSuccessful(
      defaultEvaluator.eval(Or(BooleanLiteral(false), BooleanLiteral(false))),
      BooleanLiteral(false))
    expectSuccessful(
      defaultEvaluator.eval(Or(BooleanLiteral(false), BooleanLiteral(true))),
      BooleanLiteral(true))
    expectSuccessful(
      defaultEvaluator.eval(Not(BooleanLiteral(false))),
      BooleanLiteral(true))
    expectSuccessful(
      defaultEvaluator.eval(Not(BooleanLiteral(true))),
      BooleanLiteral(false))
  }


  test("eval simple variable") {
    val id = FreshIdentifier("id").setType(Int32Type)
    expectSuccessful(
      defaultEvaluator.eval(Variable(id), Map(id -> IntLiteral(23))),
      IntLiteral(23))
  }

  test("eval with unbound variable should return EvaluatorError") {
    val id = FreshIdentifier("id").setType(Int32Type)
    val foo = FreshIdentifier("foo").setType(Int32Type)
    val res = defaultEvaluator.eval(Variable(id), Map(foo -> IntLiteral(23)))
    assert(res.isInstanceOf[EvaluationResults.EvaluatorError])
  }

  test("eval let expression") {
    val id = FreshIdentifier("id")
    expectSuccessful(
      defaultEvaluator.eval(Let(id, IntLiteral(42), Variable(id))),
      IntLiteral(42))
  }


  test("eval literal array ops") {
    expectSuccessful(
      defaultEvaluator.eval(FiniteArray(Map(), Some(IntLiteral(12)), IntLiteral(7)).setType(ArrayType(Int32Type))),
      FiniteArray(Map(), Some(IntLiteral(12)), IntLiteral(7)))
    expectSuccessful(
      defaultEvaluator.eval(
        ArrayLength(FiniteArray(Map(), Some(IntLiteral(12)), IntLiteral(7)).setType(ArrayType(Int32Type)))),
      IntLiteral(7))
    expectSuccessful(
      defaultEvaluator.eval(ArraySelect(
        FiniteArray(Seq(IntLiteral(2), IntLiteral(4), IntLiteral(7))),
        IntLiteral(1))),
      IntLiteral(4))
    expectSuccessful(
      defaultEvaluator.eval(
        ArrayUpdated(
          FiniteArray(Seq(IntLiteral(2), IntLiteral(4), IntLiteral(7))),
          IntLiteral(1),
          IntLiteral(42))),
      FiniteArray(Seq(IntLiteral(2), IntLiteral(42), IntLiteral(7))))
  }

  test("eval variable length of array") {
    val id = FreshIdentifier("id").setType(Int32Type)
    expectSuccessful(
      defaultEvaluator.eval(
        ArrayLength(
          FiniteArray(Map(), Some(IntLiteral(12)), Variable(id))
          .setType(ArrayType(Int32Type))),
        Map(id -> IntLiteral(27))),
      IntLiteral(27))
  }

  test("eval variable default value of array") {
    val id = FreshIdentifier("id").setType(Int32Type)
    expectSuccessful(
      defaultEvaluator.eval(
        FiniteArray(Map(), Some(Variable(id)), IntLiteral(7)).setType(ArrayType(Int32Type)),
        Map(id -> IntLiteral(27))),
      FiniteArray(Map(), Some(IntLiteral(27)), IntLiteral(7)))
  }
}
