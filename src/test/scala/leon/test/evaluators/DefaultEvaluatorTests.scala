/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.evaluators

import leon._
import leon.evaluators._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.Constructors._

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
    expectSuccessful(defaultEvaluator.eval(InfiniteIntegerLiteral(0)), InfiniteIntegerLiteral(0))
    expectSuccessful(defaultEvaluator.eval(InfiniteIntegerLiteral(42)), InfiniteIntegerLiteral(42))
  }

  test("eval of simple bit vector arithmetic expressions") {
    expectSuccessful(defaultEvaluator.eval(BVPlus(IntLiteral(3), IntLiteral(5))), IntLiteral(8))
    expectSuccessful(defaultEvaluator.eval(BVPlus(IntLiteral(0), IntLiteral(5))), IntLiteral(5))
    expectSuccessful(defaultEvaluator.eval(BVTimes(IntLiteral(3), IntLiteral(3))), IntLiteral(9))
  }

  test("eval bitwise operations") {
    expectSuccessful(defaultEvaluator.eval(BVAnd(IntLiteral(3), IntLiteral(1))), IntLiteral(1))
    expectSuccessful(defaultEvaluator.eval(BVAnd(IntLiteral(3), IntLiteral(3))), IntLiteral(3))
    expectSuccessful(defaultEvaluator.eval(BVAnd(IntLiteral(5), IntLiteral(3))), IntLiteral(1))
    expectSuccessful(defaultEvaluator.eval(BVAnd(IntLiteral(5), IntLiteral(4))), IntLiteral(4))
    expectSuccessful(defaultEvaluator.eval(BVAnd(IntLiteral(5), IntLiteral(2))), IntLiteral(0))

    expectSuccessful(defaultEvaluator.eval(BVOr(IntLiteral(3), IntLiteral(1))), IntLiteral(3))
    expectSuccessful(defaultEvaluator.eval(BVOr(IntLiteral(3), IntLiteral(3))), IntLiteral(3))
    expectSuccessful(defaultEvaluator.eval(BVOr(IntLiteral(5), IntLiteral(3))), IntLiteral(7))
    expectSuccessful(defaultEvaluator.eval(BVOr(IntLiteral(5), IntLiteral(4))), IntLiteral(5))
    expectSuccessful(defaultEvaluator.eval(BVOr(IntLiteral(5), IntLiteral(2))), IntLiteral(7))

    expectSuccessful(defaultEvaluator.eval(BVXOr(IntLiteral(3), IntLiteral(1))), IntLiteral(2))
    expectSuccessful(defaultEvaluator.eval(BVXOr(IntLiteral(3), IntLiteral(3))), IntLiteral(0))

    expectSuccessful(defaultEvaluator.eval(BVNot(IntLiteral(1))), IntLiteral(-2))

    expectSuccessful(defaultEvaluator.eval(BVShiftLeft(IntLiteral(3), IntLiteral(1))), IntLiteral(6))
    expectSuccessful(defaultEvaluator.eval(BVShiftLeft(IntLiteral(4), IntLiteral(2))), IntLiteral(16))

    expectSuccessful(defaultEvaluator.eval(BVLShiftRight(IntLiteral(8), IntLiteral(1))), IntLiteral(4))
    expectSuccessful(defaultEvaluator.eval(BVAShiftRight(IntLiteral(8), IntLiteral(1))), IntLiteral(4))
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
    val id = FreshIdentifier("id", Int32Type)
    expectSuccessful(
      defaultEvaluator.eval(Variable(id), Map(id -> IntLiteral(23))),
      IntLiteral(23))
  }

  test("eval with unbound variable should return EvaluatorError") {
    val id = FreshIdentifier("id", Int32Type)
    val foo = FreshIdentifier("foo", Int32Type)
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
      defaultEvaluator.eval(finiteArray(Map[Int,Expr](), Some(IntLiteral(12), IntLiteral(7)), Int32Type)),
      finiteArray(Map[Int,Expr](), Some(IntLiteral(12), IntLiteral(7)), Int32Type))
    expectSuccessful(
      defaultEvaluator.eval(
        ArrayLength(finiteArray(Map[Int,Expr](), Some(IntLiteral(12), IntLiteral(7)), Int32Type))),
      IntLiteral(7))
    expectSuccessful(
      defaultEvaluator.eval(ArraySelect(
        finiteArray(Seq(IntLiteral(2), IntLiteral(4), IntLiteral(7))),
        IntLiteral(1))),
      IntLiteral(4))
    expectSuccessful(
      defaultEvaluator.eval(
        ArrayUpdated(
          finiteArray(Seq(IntLiteral(2), IntLiteral(4), IntLiteral(7))),
          IntLiteral(1),
          IntLiteral(42))),
      finiteArray(Seq(IntLiteral(2), IntLiteral(42), IntLiteral(7))))
  }

  test("eval variable length of array") {
    val id = FreshIdentifier("id", Int32Type)
    expectSuccessful(
      defaultEvaluator.eval(
        ArrayLength(
          finiteArray(Map[Int, Expr](), Some(IntLiteral(12), Variable(id)), Int32Type)),
        Map(id -> IntLiteral(27))),
      IntLiteral(27))
  }

  test("eval variable default value of array") {
    val id = FreshIdentifier("id", Int32Type)
    expectSuccessful(
      defaultEvaluator.eval(
        finiteArray(Map[Int, Expr](), Some(Variable(id), IntLiteral(7)), Int32Type),
        Map(id -> IntLiteral(27))),
      finiteArray(Map[Int, Expr](), Some(IntLiteral(27), IntLiteral(7)), Int32Type))
  }

}
