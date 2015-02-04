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
    expectSuccessful(defaultEvaluator.eval(InfiniteIntegerLiteral(0)), InfiniteIntegerLiteral(0))
    expectSuccessful(defaultEvaluator.eval(InfiniteIntegerLiteral(42)), InfiniteIntegerLiteral(42))
    expectSuccessful(defaultEvaluator.eval(UnitLiteral()), UnitLiteral())
  }

  test("eval of simple bit vector arithmetic expressions") {
    expectSuccessful(defaultEvaluator.eval(BVPlus(IntLiteral(3), IntLiteral(5))), IntLiteral(8))
    expectSuccessful(defaultEvaluator.eval(BVPlus(IntLiteral(0), IntLiteral(5))), IntLiteral(5))
    expectSuccessful(defaultEvaluator.eval(BVTimes(IntLiteral(3), IntLiteral(3))), IntLiteral(9))
  }

  test("eval of simple arithmetic expressions") {
    expectSuccessful(
      defaultEvaluator.eval(Plus(InfiniteIntegerLiteral(3), InfiniteIntegerLiteral(5))), 
      InfiniteIntegerLiteral(8))
    expectSuccessful(
      defaultEvaluator.eval(Minus(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(2))), 
      InfiniteIntegerLiteral(5))
    expectSuccessful(
      defaultEvaluator.eval(UMinus(InfiniteIntegerLiteral(7))),
      InfiniteIntegerLiteral(-7))
    expectSuccessful(
      defaultEvaluator.eval(Times(InfiniteIntegerLiteral(2), InfiniteIntegerLiteral(3))), 
      InfiniteIntegerLiteral(6))
    expectSuccessful(
      defaultEvaluator.eval(Modulo(InfiniteIntegerLiteral(10), InfiniteIntegerLiteral(3))), 
      InfiniteIntegerLiteral(1))
  }
}
