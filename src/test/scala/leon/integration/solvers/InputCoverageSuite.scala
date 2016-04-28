package leon.integration.solvers

import org.scalatest.FunSuite
import org.scalatest.Matchers
import leon.test.helpers.ExpressionsDSL
import leon.solvers.string.StringSolver
import leon.purescala.Common.FreshIdentifier
import leon.purescala.Common.Identifier
import leon.purescala.Expressions._
import leon.purescala.Definitions._
import leon.purescala.DefOps
import leon.purescala.ExprOps
import leon.purescala.Types._
import leon.purescala.TypeOps
import leon.purescala.Constructors._
import leon.synthesis.rules.{StringRender, TypedTemplateGenerator}
import scala.collection.mutable.{HashMap => MMap}
import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global
import org.scalatest.concurrent.Timeouts
import org.scalatest.concurrent.ScalaFutures
import org.scalatest.time.SpanSugar._
import org.scalatest.FunSuite
import org.scalatest.concurrent.Timeouts
import org.scalatest.concurrent.ScalaFutures
import org.scalatest.time.SpanSugar._
import leon.purescala.Types.Int32Type
import leon.test.LeonTestSuiteWithProgram
import leon.synthesis.SourceInfo
import leon.synthesis.CostModels
import leon.synthesis.graph.AndNode
import leon.synthesis.SearchContext
import leon.synthesis.Synthesizer
import leon.synthesis.SynthesisSettings
import leon.synthesis.RuleApplication
import leon.synthesis.RuleClosed
import leon.evaluators._
import leon.LeonContext
import leon.synthesis.rules.DetupleInput
import leon.synthesis.Rules
import leon.solvers.ModelBuilder
import scala.language.implicitConversions
import leon.LeonContext
import leon.test.LeonTestSuiteWithProgram
import leon.test.helpers.ExpressionsDSL
import leon.synthesis.disambiguation.InputCoverage
import leon.test.helpers.ExpressionsDSLProgram
import leon.test.helpers.ExpressionsDSLVariables
import leon.purescala.Extractors._

class InputCoverageSuite extends LeonTestSuiteWithProgram with Matchers with ScalaFutures with ExpressionsDSLProgram with ExpressionsDSLVariables {

  //override a because it comes from both Matchers and ExpressionsDSLVariables
  override val a = null

  override val leonOpts = List("--solvers=smt-cvc4")

  val sources = List("""
    |import leon.lang._
    |import leon.collection._
    |import leon.lang.synthesis._
    |import leon.annotation._
    |
    |object InputCoverageSuite {
    |  def dummy = 2
    |  def withIf(cond: Boolean) = {
    |    if(cond) {
    |      1
    |    } else {
    |      2
    |    }
    |  }
    |  
    |  def withIfInIf(cond: Boolean) = {
    |    if(if(cond) false else true) {
    |      1
    |    } else {
    |      2
    |    }
    |  }
    |  
    |  sealed abstract class A
    |  case class B() extends A
    |  case class C(a: String, tail: A) extends A
    |  case class D(a: String, tail: A, b: String) extends A
    |  
    |  def withMatch(a: A): String = {
    |    a match {
    |      case B() => "B"
    |      case C(a, C(b, tail)) => b.toString + withMatch(tail) + a.toString
    |      case C(a, tail) => withMatch(tail) + a.toString
    |      case D(a, tail, b) => a + withMatch(tail) + b
    |    }
    |  }
    |  
    |  def withCoveredFun1(input: Int) = {
    |    withCoveredFun2(input - 5) + withCoveredFun2(input + 5)
    |  }
    |  
    |  def withCoveredFun2(input: Int) = {
    |    if(input > 0) {
    |      2
    |    } else {
    |      0
    |    }
    |  }
    |  
    |  def withCoveredFun3(input: Int) = {
    |    withCoveredFun2(withCoveredFun2(input + 5))
    |  }
    |  
    |  def coveredCond(a: Boolean, b: Boolean, c: Boolean, d: Boolean) = {
    |    if(a || b) {
    |      if(c && d) {
    |        1
    |      } else if(c) {
    |        2
    |      } else {
    |        3
    |      }
    |    } else if(!a && c) {
    |      4
    |    } else 5
    |  }
    |  
    |}""".stripMargin)
    
  test("wrapBranch should wrap expressions if they are not already containing wrapped calls"){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    val dummy = funDef("InputCoverageSuite.dummy")
    val coverage = new InputCoverage(dummy, Set(dummy))
    val simpleExpr = Plus(IntLiteral(1), b)
    coverage.wrapBranch((simpleExpr, Some(Seq(p.id, q.id)))) should equal ((simpleExpr, Some(Seq(p.id, q.id))))
    coverage.wrapBranch((simpleExpr, None)) match {
      case (covered, Some(ids)) =>
        ids should have size 1
        covered should equal (Tuple(Seq(simpleExpr, Variable(ids.head))))
      case _ =>
        fail("No ids added")
    }
  }
  
  test("If-coverage should work"){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withIf = funDef("InputCoverageSuite.withIf")
    val coverage = new InputCoverage(withIf, Set(withIf))
    val expr = withIf.body.get
    
    coverage.markBranches(expr) match {
      case (res, Some(ids)) =>
        ids should have size 2
        expr match {
          case IfExpr(cond, thenn, elze) =>
            res should equal (IfExpr(cond, Tuple(Seq(thenn, Variable(ids(0)))), Tuple(Seq(elze, Variable(ids(1))))))
          case _ => fail(s"$expr is not an IfExpr")
        }
      case _ =>
        fail("No ids added")
    }
  }
  
  test("If-cond-coverage should work"){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withIfInIf = funDef("InputCoverageSuite.withIfInIf")
    val coverage = new InputCoverage(withIfInIf, Set(withIfInIf))
    val expr = withIfInIf.body.get
    
    coverage.markBranches(expr) match {
      case (res, None) => fail("No ids added")
      case (res, Some(ids)) =>
        ids should have size 4
        expr match {
          case IfExpr(IfExpr(cond, t1, e1), t2, e2) =>
            res match {
              case MatchExpr(IfExpr(c, t1, e1), Seq(MatchCase(TuplePattern(None, s), None, IfExpr(c2, t2, e2)))) if s.size == 2 =>
              case _ => fail("should have a shape like (if() else ) match { case (a, b) => if(...) else }")
            }
          case _ => fail(s"$expr is not an IfExpr")
        }
    }
  }
  
  test("Match coverage should work with recursive functions") { ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withMatch = funDef("InputCoverageSuite.withMatch")
    val coverage = new InputCoverage(withMatch, Set(withMatch))
    val expr = withMatch.body.get
    
    coverage.markBranches(expr) match {
      case (res, None) => fail("No ids added")
      case (res, Some(ids)) =>
        withClue(res.toString) {
          ids should have size 4
        }
    }
  }
  
  test("fundef combination-coverage should work"){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withCoveredFun1 = funDef("InputCoverageSuite.withCoveredFun1")
    val withCoveredFun2 = funDef("InputCoverageSuite.withCoveredFun2")
    val coverage = new InputCoverage(withCoveredFun1, Set(withCoveredFun1, withCoveredFun2))
    val expr = withCoveredFun1.body.get
    
    coverage.markBranches(expr) match {
      case (res, Some(ids)) if ids.size > 0 =>
        withClue(res.toString) {
          fail(s"Should have not added any ids, but got $ids")
        }
      case (res, _) =>
    }
  }
  
  test("fundef composition-coverage should work"){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withCoveredFun2 = funDef("InputCoverageSuite.withCoveredFun2")
    val withCoveredFun3 = funDef("InputCoverageSuite.withCoveredFun3")
    val coverage = new InputCoverage(withCoveredFun3, Set(withCoveredFun3, withCoveredFun2))
    val expr = withCoveredFun3.body.get
    
    coverage.markBranches(expr) match {
      case (res, None) => fail("No ids added")
      case (res, Some(ids)) =>
    }
  }
  
  test("input coverage for booleans should find all of them") { ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withIf = funDef("InputCoverageSuite.withIf")
    val coverage = new InputCoverage(withIf, Set(withIf))
    coverage.result().toSet should equal (Set(Seq(b(true)), Seq(b(false))))
  }
  
  test("input coverage for ADT should find all of them") { ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withMatch = funDef("InputCoverageSuite.withMatch")
    val coverage = new InputCoverage(withMatch, Set(withMatch))
    coverage.minimizeExamples = false
    val res = coverage.result().toSet
    res should have size 4
    
    coverage.minimizeExamples = true
    val res2 = coverage.result().toSet
    res2 should have size 3
  }
  
  test("input coverage for boolean, disjunctions and conjunctions should find all of them") { ctxprogram =>
    implicit val (c, p) = ctxprogram
    val coveredCond = funDef("InputCoverageSuite.coveredCond")
    val coverage = new InputCoverage(coveredCond, Set(coveredCond))
    coverage.minimizeExamples = true
    val res2 = coverage.result().toSet
    res2 should have size 5
  }

  test("input coverage for combined functions should find all of them") { ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withCoveredFun1 = funDef("InputCoverageSuite.withCoveredFun1")
    val withCoveredFun2 = funDef("InputCoverageSuite.withCoveredFun2")
    val coverage = new InputCoverage(withCoveredFun1, Set(withCoveredFun1, withCoveredFun2))
    val res = coverage.result().toSet.toSeq
    if(res.size == 1) {
      val Seq(IntLiteral(a)) = res(0)
      withClue(s"a=$a") {
        assert(a + 5 > 0 || a - 5 > 0, "At least one of the two examples should cover the positive case")
        assert(a + 5 <= 0 || a - 5 <= 0, "At least one of the two examples should cover the negative case")
      }
    } else {
      res should have size 2
      val Seq(IntLiteral(a)) = res(0)
      val Seq(IntLiteral(b)) = res(1)
      withClue(s"a=$a, b=$b") {
        assert(a + 5 > 0 || b + 5 > 0 || a - 5 > 0 || b - 5 > 0 , "At least one of the two examples should cover the positive case")
        assert(a + 5 <= 0 || b + 5 <= 0 || a - 5 <= 0 || b - 5 <= 0 , "At least one of the two examples should cover the negative case")
      }
    }
  }
  
  test("input coverage for composed functions should find all of them") { ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withCoveredFun3 = funDef("InputCoverageSuite.withCoveredFun3")
    val withCoveredFun2 = funDef("InputCoverageSuite.withCoveredFun2")
    val coverage = new InputCoverage(withCoveredFun3, Set(withCoveredFun3, withCoveredFun2))
    val res = coverage.result().toSet.toSeq
    def withCoveredFun2Impl(i: Int) = if(i > 0) 2 else 0
    if(res.size == 1) {
      val Seq(IntLiteral(a)) = res(0)
      withClue(s"a=$a") {
        assert(a + 5 > 0 || withCoveredFun2Impl(a + 5) > 0, "At least one of the two examples should cover the positive case")
        assert(a + 5 <= 0 || withCoveredFun2Impl(a + 5) <= 0, "At least one of the two examples should cover the negative case")
      }
    } else {
      res should have size 2
      val Seq(IntLiteral(a)) = res(0)
      val Seq(IntLiteral(b)) = res(1)
      withClue(s"a=$a, b=$b") {
        assert(a + 5 > 0 || withCoveredFun2Impl(a + 5) > 0 || b + 5 > 0 || withCoveredFun2Impl(b + 5) > 0, "At least one of the two examples should cover the positive case")
        assert(a + 5 <= 0 || withCoveredFun2Impl(a + 5) <= 0 || b + 5 <= 0 || withCoveredFun2Impl(b + 5) <= 0, "At least one of the two examples should cover the negative case")
      }
    }
  }
}
