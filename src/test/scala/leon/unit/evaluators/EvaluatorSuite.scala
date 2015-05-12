/* Copyright 2009-2015 EPFL, Lausanne */

package leon.unit.allEvaluators

import leon._
import leon.test._
import leon.evaluators._

import leon.utils.{TemporaryInputPhase, PreprocessingPhase}
import leon.frontends.scalac.ExtractionPhase

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.DefOps._
import leon.purescala.Types._
import leon.purescala.Extractors._
import leon.purescala.Constructors._
import leon.codegen._

class EvaluatorSuite extends LeonTestSuite with helpers.ExpressionsDSL {

  implicit val pgm = Program.empty

  def normalEvaluators(implicit ctx: LeonContext, pgm: Program): List[Evaluator] = {
    List(
      new DefaultEvaluator(ctx, pgm)
    )
  }

  def codegenEvaluators(implicit ctx: LeonContext, pgm: Program): List[Evaluator] = {
    List(
      new CodeGenEvaluator(ctx, pgm)
    )
  }

  def allEvaluators(implicit ctx: LeonContext, pgm: Program): List[Evaluator] = {
    normalEvaluators ++ codegenEvaluators
  }


  test("Literals") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, BooleanLiteral(true))         === BooleanLiteral(true)
      eval(e, BooleanLiteral(false))        === BooleanLiteral(false)
      eval(e, IntLiteral(0))                === IntLiteral(0)
      eval(e, IntLiteral(42))               === IntLiteral(42)
      eval(e, UnitLiteral())                === UnitLiteral()
      eval(e, InfiniteIntegerLiteral(0))    === InfiniteIntegerLiteral(0)
      eval(e, InfiniteIntegerLiteral(42))   === InfiniteIntegerLiteral(42)
      eval(e, FractionalLiteral(0 ,1))      === FractionalLiteral(0 ,1)
      eval(e, FractionalLiteral(42 ,1))     === FractionalLiteral(42, 1)
      eval(e, FractionalLiteral(26, 3))     === FractionalLiteral(26, 3)
    }
  }

  test("BitVector Arithmetic") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, BVPlus(IntLiteral(3), IntLiteral(5)))  === IntLiteral(8)
      eval(e, BVPlus(IntLiteral(0), IntLiteral(5)))  === IntLiteral(5)
      eval(e, BVTimes(IntLiteral(3), IntLiteral(3))) === IntLiteral(9)
    }
  }

  test("eval bitwise operations") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, BVAnd(IntLiteral(3), IntLiteral(1))) === IntLiteral(1)
      eval(e, BVAnd(IntLiteral(3), IntLiteral(3))) === IntLiteral(3)
      eval(e, BVAnd(IntLiteral(5), IntLiteral(3))) === IntLiteral(1)
      eval(e, BVAnd(IntLiteral(5), IntLiteral(4))) === IntLiteral(4)
      eval(e, BVAnd(IntLiteral(5), IntLiteral(2))) === IntLiteral(0)

      eval(e, BVOr(IntLiteral(3), IntLiteral(1))) === IntLiteral(3)
      eval(e, BVOr(IntLiteral(3), IntLiteral(3))) === IntLiteral(3)
      eval(e, BVOr(IntLiteral(5), IntLiteral(3))) === IntLiteral(7)
      eval(e, BVOr(IntLiteral(5), IntLiteral(4))) === IntLiteral(5)
      eval(e, BVOr(IntLiteral(5), IntLiteral(2))) === IntLiteral(7)

      eval(e, BVXOr(IntLiteral(3), IntLiteral(1))) === IntLiteral(2)
      eval(e, BVXOr(IntLiteral(3), IntLiteral(3))) === IntLiteral(0)

      eval(e, BVNot(IntLiteral(1))) === IntLiteral(-2)

      eval(e, BVShiftLeft(IntLiteral(3), IntLiteral(1))) === IntLiteral(6)
      eval(e, BVShiftLeft(IntLiteral(4), IntLiteral(2))) === IntLiteral(16)

      eval(e, BVLShiftRight(IntLiteral(8), IntLiteral(1))) === IntLiteral(4)
      eval(e, BVAShiftRight(IntLiteral(8), IntLiteral(1))) === IntLiteral(4)
    }
  }

  test("Arithmetic") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, Plus(InfiniteIntegerLiteral(3), InfiniteIntegerLiteral(5)))  === InfiniteIntegerLiteral(8)
      eval(e, Minus(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(2))) === InfiniteIntegerLiteral(5)
      eval(e, UMinus(InfiniteIntegerLiteral(7)))                           === InfiniteIntegerLiteral(-7)
      eval(e, Times(InfiniteIntegerLiteral(2), InfiniteIntegerLiteral(3))) === InfiniteIntegerLiteral(6)
    }
  }

  test("BigInt Modulo and Remainder") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, Division(InfiniteIntegerLiteral(10), InfiniteIntegerLiteral(3)))   === InfiniteIntegerLiteral(3)
      eval(e, Remainder(InfiniteIntegerLiteral(10), InfiniteIntegerLiteral(3)))  === InfiniteIntegerLiteral(1)
      eval(e, Modulo(InfiniteIntegerLiteral(10), InfiniteIntegerLiteral(3)))     === InfiniteIntegerLiteral(1)

      eval(e, Division(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(3)))   === InfiniteIntegerLiteral(0)
      eval(e, Remainder(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(3)))  === InfiniteIntegerLiteral(-1)

      eval(e, Modulo(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(3)))     === InfiniteIntegerLiteral(2)

      eval(e, Division(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(-3)))  === InfiniteIntegerLiteral(0)
      eval(e, Remainder(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(-3))) === InfiniteIntegerLiteral(-1)
      eval(e, Modulo(InfiniteIntegerLiteral(-1), InfiniteIntegerLiteral(-3)))    === InfiniteIntegerLiteral(2)

      eval(e, Division(InfiniteIntegerLiteral(1), InfiniteIntegerLiteral(-3)))   === InfiniteIntegerLiteral(0)
      eval(e, Remainder(InfiniteIntegerLiteral(1), InfiniteIntegerLiteral(-3)))  === InfiniteIntegerLiteral(1)
      eval(e, Modulo(InfiniteIntegerLiteral(1), InfiniteIntegerLiteral(-3)))     === InfiniteIntegerLiteral(1)
    }
  }

  test("Int Comparisons") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, GreaterEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4)))  === BooleanLiteral(true)
      eval(e, GreaterEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7)))  === BooleanLiteral(true)
      eval(e, GreaterEquals(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7)))  === BooleanLiteral(false)

      eval(e, GreaterThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4)))    === BooleanLiteral(true)
      eval(e, GreaterThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7)))    === BooleanLiteral(false)
      eval(e, GreaterThan(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7)))    === BooleanLiteral(false)

      eval(e, LessEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4)))     === BooleanLiteral(false)
      eval(e, LessEquals(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7)))     === BooleanLiteral(true)
      eval(e, LessEquals(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7)))     === BooleanLiteral(true)

      eval(e, LessThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(4)))       === BooleanLiteral(false)
      eval(e, LessThan(InfiniteIntegerLiteral(7), InfiniteIntegerLiteral(7)))       === BooleanLiteral(false)
      eval(e, LessThan(InfiniteIntegerLiteral(4), InfiniteIntegerLiteral(7)))       === BooleanLiteral(true)
    }
  }


  test("Int Modulo and Remainder") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, BVDivision(IntLiteral(10), IntLiteral(3)))    === IntLiteral(3)
      eval(e, BVRemainder(IntLiteral(10), IntLiteral(3)))   === IntLiteral(1)

      eval(e, BVDivision(IntLiteral(-1), IntLiteral(3)))    === IntLiteral(0)
      eval(e, BVRemainder(IntLiteral(-1), IntLiteral(3)))   === IntLiteral(-1)

      eval(e, BVDivision(IntLiteral(-1), IntLiteral(-3)))   === IntLiteral(0)
      eval(e, BVRemainder(IntLiteral(-1), IntLiteral(-3)))  === IntLiteral(-1)

      eval(e, BVDivision(IntLiteral(1), IntLiteral(-3)))    === IntLiteral(0)
      eval(e, BVRemainder(IntLiteral(1), IntLiteral(-3)))   === IntLiteral(1)
    }
  }

  test("Boolean Operations") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, And(BooleanLiteral(true), BooleanLiteral(true)))      === BooleanLiteral(true)
      eval(e, And(BooleanLiteral(true), BooleanLiteral(false)))     === BooleanLiteral(false)
      eval(e, And(BooleanLiteral(false), BooleanLiteral(false)))    === BooleanLiteral(false)
      eval(e, And(BooleanLiteral(false), BooleanLiteral(true)))     === BooleanLiteral(false)
      eval(e, Or(BooleanLiteral(true), BooleanLiteral(true)))       === BooleanLiteral(true)
      eval(e, Or(BooleanLiteral(true), BooleanLiteral(false)))      === BooleanLiteral(true)
      eval(e, Or(BooleanLiteral(false), BooleanLiteral(false)))     === BooleanLiteral(false)
      eval(e, Or(BooleanLiteral(false), BooleanLiteral(true)))      === BooleanLiteral(true)
      eval(e, Not(BooleanLiteral(false)))                           === BooleanLiteral(true)
      eval(e, Not(BooleanLiteral(true)))                            === BooleanLiteral(false)
    }
  }

  test("Real Arightmetic") { implicit fix =>
    for (e <- allEvaluators) {
      eval(e, RealPlus(FractionalLiteral(2, 3), FractionalLiteral(1, 3))) === FractionalLiteral(1, 1)
      eval(e, RealMinus(FractionalLiteral(1, 1), FractionalLiteral(1, 4))) === FractionalLiteral(3, 4)
      eval(e, RealUMinus(FractionalLiteral(7, 1))) === FractionalLiteral(-7, 1)
      eval(e, RealTimes(FractionalLiteral(2, 3), FractionalLiteral(1, 3))) === FractionalLiteral(2, 9)
    }
  }

  test("Real Comparisons") { implicit fix =>
    for(e <- allEvaluators) {
      eval(e, GreaterEquals(FractionalLiteral(7, 1), FractionalLiteral(4, 2))) === BooleanLiteral(true)
      eval(e, GreaterEquals(FractionalLiteral(7, 2), FractionalLiteral(49, 13))) === BooleanLiteral(false)

      eval(e, GreaterThan(FractionalLiteral(49, 13), FractionalLiteral(7, 2))) === BooleanLiteral(true)
      eval(e, GreaterThan(FractionalLiteral(49, 14), FractionalLiteral(7, 2))) === BooleanLiteral(false)
      eval(e, GreaterThan(FractionalLiteral(4, 2), FractionalLiteral(7, 1))) === BooleanLiteral(false)

      eval(e, LessEquals(FractionalLiteral(7, 1), FractionalLiteral(4, 2))) === BooleanLiteral(false)
      eval(e, LessEquals(FractionalLiteral(7, 2), FractionalLiteral(49, 13))) === BooleanLiteral(true)

      eval(e, LessThan(FractionalLiteral(49, 13), FractionalLiteral(7, 2))) === BooleanLiteral(false)
      eval(e, LessThan(FractionalLiteral(49, 14), FractionalLiteral(7, 2))) === BooleanLiteral(false)
      eval(e, LessThan(FractionalLiteral(4, 2), FractionalLiteral(7, 1))) === BooleanLiteral(true)
    }
  }

  test("Simple Variable") { implicit fix =>
    for(e <- allEvaluators) {
      val id = FreshIdentifier("id", Int32Type)

      eval(e, Variable(id), Map(id -> IntLiteral(23))) === IntLiteral(23)
    }
  }

  test("Undefined Variable") { implicit fix =>
    for(e <- allEvaluators) {
      val id = FreshIdentifier("id", Int32Type)
      val foo = FreshIdentifier("foo", Int32Type)

      eval(e, Variable(id), Map(foo -> IntLiteral(23))).failed
    }
  }

  test("Let") { implicit fix =>
    for(e <- normalEvaluators) {
      val id = FreshIdentifier("id")
      eval(e, Let(id, IntLiteral(42), Variable(id))) === IntLiteral(42)
    }
  }

  def eqArray(a1: Expr, a2: Expr) = (a1, a2) match {
    case (FiniteArray(es1, d1, IntLiteral(l1)), FiniteArray(es2, d2, IntLiteral(l2))) =>
      assert(l1 === l2)
      for (i <- 0 until l1) {
        val v1 = es1.get(i).orElse(d1)
        val v2 = es2.get(i).orElse(d2)
        assert(v1 === v2)
      }
    case (e, _) =>
      fail("Expected array, got "+e)
  }

  test("Array Operations") { implicit fix =>
    for (e <- allEvaluators) {
      eqArray(eval(e, finiteArray(Map[Int,Expr](), Some(IntLiteral(12), IntLiteral(7)), Int32Type)).res,
                      finiteArray(Map[Int,Expr](), Some(IntLiteral(12), IntLiteral(7)), Int32Type))

      eval(e, ArrayLength(finiteArray(Map[Int,Expr](), Some(IntLiteral(12), IntLiteral(7)), Int32Type))) ===
                      IntLiteral(7)

      eval(e, ArraySelect(finiteArray(Seq(IntLiteral(2), IntLiteral(4), IntLiteral(7))), IntLiteral(1))) ===
                      IntLiteral(4)

      eqArray(eval(e, ArrayUpdated( finiteArray(Seq(IntLiteral(2), IntLiteral(4), IntLiteral(7))), IntLiteral(1), IntLiteral(42))).res,
                      finiteArray(Seq(IntLiteral(2), IntLiteral(42), IntLiteral(7))))

    }
  }

  test("Array with variable length") { implicit fix =>
    // This does not work with CodegenEvaluator
    for (e <- normalEvaluators) {
      val len = FreshIdentifier("len", Int32Type)
      eval(e, ArrayLength(finiteArray(Map[Int, Expr](), Some(IntLiteral(12), Variable(len)), Int32Type)), Map(len -> IntLiteral(27))) ===
        IntLiteral(27)
    }
  }

  test("Array Default Value") { implicit fix  =>
    for (e <- allEvaluators) {
      val id = FreshIdentifier("id", Int32Type)
      eqArray(eval(e, finiteArray(Map[Int, Expr](), Some(Variable(id), IntLiteral(7)), Int32Type), Map(id -> IntLiteral(27))).res,
                      finiteArray(Map[Int, Expr](), Some(IntLiteral(27), IntLiteral(7)), Int32Type))
    }
  }

  abstract class EvalDSL {
    def res: Expr
    def ===(res: Expr): Unit
    def failed: Unit = {}
    def success: Expr = res
  }

  case class Success(expr: Expr, env: Map[Identifier, Expr], evaluator: Evaluator, res: Expr) extends EvalDSL {
    override def failed = {
      fail(s"Evaluation of '$expr' with '$evaluator' (and env $env) should have failed")
    }

    def ===(exp: Expr) = {
      assert(res === exp)
    }
  }

  case class Failed(expr: Expr, env: Map[Identifier, Expr], evaluator: Evaluator, err: String) extends EvalDSL {
    override def success = {
      fail(s"Evaluation of '$expr' with '$evaluator' (and env $env) should have succeeded but failed with $err")
    }

    def res = success

    def ===(res: Expr) = success
  }

  def eval(e: Evaluator, toEval: Expr, env: Map[Identifier, Expr] = Map()): EvalDSL = {
    e.eval(toEval, env) match {
      case EvaluationResults.Successful(res)     => Success(toEval, env, e, res)
      case EvaluationResults.RuntimeError(err)   => Failed(toEval, env, e, err)
      case EvaluationResults.EvaluatorError(err) => Failed(toEval, env, e, err)
    }
  }
}
