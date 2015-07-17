/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.evaluators

import leon._
import leon.evaluators._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.Constructors._

class DefaultEvaluatorSuite extends leon.test.LeonTestSuite {
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
    expectSuccessful(defaultEvaluator.eval(RealLiteral(0)), RealLiteral(0))
    expectSuccessful(defaultEvaluator.eval(RealLiteral(42)), RealLiteral(42))
    expectSuccessful(defaultEvaluator.eval(RealLiteral(13.255)), RealLiteral(13.255))
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
  }

  test("Eval of division, remainder and modulo semantics for BigInt") {
    expectSuccessful(
      defaultEvaluator.eval(Division(InfiniteIntegerLiteral(10), InfiniteIntegerLiteral(3))), 
      InfiniteIntegerLiteral(3))
    expectSuccessful(
      defaultEvaluator.eval(Remainder(InfiniteIntegerLiteral(10), InfiniteIntegerLiteral(3))), 
      InfiniteIntegerLiteral(1))
    expectSuccessful(
      defaultEvaluator.eval(Modulo(InfiniteIntegerLiteral(10), InfiniteIntegerLiteral(3))), 
      InfiniteIntegerLiteral(1))

    expectSuccessful(
      defaultEvaluator.eval(Division(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(3))), 
      InfiniteIntegerLiteral(0))
    expectSuccessful(
      defaultEvaluator.eval(Remainder(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(3))), 
      InfiniteIntegerLiteral(-1))
    expectSuccessful(
      defaultEvaluator.eval(Modulo(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(3))), 
      InfiniteIntegerLiteral(2))

    expectSuccessful(
      defaultEvaluator.eval(Division(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(-3))), 
      InfiniteIntegerLiteral(0))
    expectSuccessful(
      defaultEvaluator.eval(Remainder(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(-3))), 
      InfiniteIntegerLiteral(-1))
    expectSuccessful(
      defaultEvaluator.eval(Modulo(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(-3))), 
      InfiniteIntegerLiteral(2))

    expectSuccessful(
      defaultEvaluator.eval(Division(InfiniteIntegerLiteral(1), InfiniteIntegerLiteral(-3))), 
      InfiniteIntegerLiteral(0))
    expectSuccessful(
      defaultEvaluator.eval(Remainder(InfiniteIntegerLiteral(1), InfiniteIntegerLiteral(-3))), 
      InfiniteIntegerLiteral(1))
    expectSuccessful(
      defaultEvaluator.eval(Modulo(InfiniteIntegerLiteral(1), InfiniteIntegerLiteral(-3))), 
      InfiniteIntegerLiteral(1))
  }

  test("eval of simple arithmetic comparisons over integers") {
    expectSuccessful(
      defaultEvaluator.eval(GreaterEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4))), BooleanLiteral(true)
    )
    expectSuccessful(
      defaultEvaluator.eval(GreaterEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7))), BooleanLiteral(true)
    )
    expectSuccessful(
      defaultEvaluator.eval(GreaterEquals(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7))), BooleanLiteral(false)
    )

    expectSuccessful(
      defaultEvaluator.eval(GreaterThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4))), BooleanLiteral(true)
    )
    expectSuccessful(
      defaultEvaluator.eval(GreaterThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7))), BooleanLiteral(false)
    )
    expectSuccessful(
      defaultEvaluator.eval(GreaterThan(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7))), BooleanLiteral(false)
    )

    expectSuccessful(
      defaultEvaluator.eval(LessEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4))), BooleanLiteral(false)
    )
    expectSuccessful(
      defaultEvaluator.eval(LessEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7))), BooleanLiteral(true)
    )
    expectSuccessful(
      defaultEvaluator.eval(LessEquals(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7))), BooleanLiteral(true)
    )

    expectSuccessful(
      defaultEvaluator.eval(LessThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4))), BooleanLiteral(false)
    )
    expectSuccessful(
      defaultEvaluator.eval(LessThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7))), BooleanLiteral(false)
    )
    expectSuccessful(
      defaultEvaluator.eval(LessThan(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7))), BooleanLiteral(true)
    )
  }


  test("Eval of division and remainder semantics for bit vectors") {
    expectSuccessful(
      defaultEvaluator.eval(BVDivision(IntLiteral(10), IntLiteral(3))), 
      IntLiteral(3))
    expectSuccessful(
      defaultEvaluator.eval(BVRemainder(IntLiteral(10), IntLiteral(3))), 
      IntLiteral(1))

    expectSuccessful(
      defaultEvaluator.eval(BVDivision(IntLiteral(-1), IntLiteral(3))), 
      IntLiteral(0))
    expectSuccessful(
      defaultEvaluator.eval(BVRemainder(IntLiteral(-1), IntLiteral(3))), 
      IntLiteral(-1))

    expectSuccessful(
      defaultEvaluator.eval(BVDivision(IntLiteral(-1), IntLiteral(-3))), 
      IntLiteral(0))
    expectSuccessful(
      defaultEvaluator.eval(BVRemainder(IntLiteral(-1), IntLiteral(-3))), 
      IntLiteral(-1))

    expectSuccessful(
      defaultEvaluator.eval(BVDivision(IntLiteral(1), IntLiteral(-3))), 
      IntLiteral(0))
    expectSuccessful(
      defaultEvaluator.eval(BVRemainder(IntLiteral(1), IntLiteral(-3))), 
      IntLiteral(1))
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

  test("eval of simple arithmetic expressions over real") {
    expectSuccessful(
      defaultEvaluator.eval(RealPlus(RealLiteral(3), RealLiteral(5))), 
      RealLiteral(8))
    expectSuccessful(
      defaultEvaluator.eval(RealMinus(RealLiteral(7), RealLiteral(2))), 
      RealLiteral(5))
    expectSuccessful(
      defaultEvaluator.eval(RealUMinus(RealLiteral(7))),
      RealLiteral(-7))
    expectSuccessful(
      defaultEvaluator.eval(RealTimes(RealLiteral(2), RealLiteral(3))), 
      RealLiteral(6))

    expectSuccessful(
      defaultEvaluator.eval(RealPlus(RealLiteral(2.5), RealLiteral(3.5))), 
      RealLiteral(6))
  }

  test("eval of simple arithmetic comparisons over real") {
    expectSuccessful(
      defaultEvaluator.eval(GreaterEquals(RealLiteral(7), RealLiteral(4))), BooleanLiteral(true)
    )
    expectSuccessful(
      defaultEvaluator.eval(GreaterEquals(RealLiteral(7), RealLiteral(7))), BooleanLiteral(true)
    )
    expectSuccessful(
      defaultEvaluator.eval(GreaterEquals(RealLiteral(4), RealLiteral(7))), BooleanLiteral(false)
    )

    expectSuccessful(
      defaultEvaluator.eval(GreaterThan(RealLiteral(7), RealLiteral(4))), BooleanLiteral(true)
    )
    expectSuccessful(
      defaultEvaluator.eval(GreaterThan(RealLiteral(7), RealLiteral(7))), BooleanLiteral(false)
    )
    expectSuccessful(
      defaultEvaluator.eval(GreaterThan(RealLiteral(4), RealLiteral(7))), BooleanLiteral(false)
    )

    expectSuccessful(
      defaultEvaluator.eval(LessEquals(RealLiteral(7), RealLiteral(4))), BooleanLiteral(false)
    )
    expectSuccessful(
      defaultEvaluator.eval(LessEquals(RealLiteral(7), RealLiteral(7))), BooleanLiteral(true)
    )
    expectSuccessful(
      defaultEvaluator.eval(LessEquals(RealLiteral(4), RealLiteral(7))), BooleanLiteral(true)
    )

    expectSuccessful(
      defaultEvaluator.eval(LessThan(RealLiteral(7), RealLiteral(4))), BooleanLiteral(false)
    )
    expectSuccessful(
      defaultEvaluator.eval(LessThan(RealLiteral(7), RealLiteral(7))), BooleanLiteral(false)
    )
    expectSuccessful(
      defaultEvaluator.eval(LessThan(RealLiteral(4), RealLiteral(7))), BooleanLiteral(true)
    )
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
