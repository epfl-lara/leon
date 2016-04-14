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
    |  case class C(a: Int, tail: A) extends A
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
          res match {
            case MatchExpr(scrut,
                   Seq(
                       MatchCase(CaseClassPattern(_, _, Seq()), None, rhs1),
                       MatchCase(CaseClassPattern(_, _, _), None, rhs2),
                       MatchCase(CaseClassPattern(_, _, _), None, rhs3),
                       MatchCase(CaseClassPattern(_, _, _), None, rhs4))
            ) =>
              rhs1 match {
                case Tuple(Seq(_, Variable(b))) => b shouldEqual ids(0)
                case _ => fail(s"$rhs1 should be a Tuple")
              }
              rhs2 match {
                case LetTuple(_, _, Tuple(Seq(_, Or(Seq(_, Variable(b)))))) => b shouldEqual ids(1)
                case _ => fail(s"$rhs2 should be a val + tuple like val ... = ... ; (..., ... || ${ids(1)})")
              }
              
            case _ => fail(s"$res does not have the format a match { case B() => .... x 4 }")
          }
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
        res match {
          case MatchExpr(funCall, Seq(
                MatchCase(TuplePattern(None, Seq(WildcardPattern(Some(a1)), WildcardPattern(Some(b1)))), None,
                  MatchExpr(funCall2, Seq(
                    MatchCase(TuplePattern(None, Seq(WildcardPattern(Some(a2)), WildcardPattern(Some(b2)))), None,
                      Tuple(Seq(BVPlus(Variable(ida1), Variable(ida2)), Or(Seq(Variable(idb1), Variable(idb2)))))
                )
              ))))) =>
            withClue(res.toString) {
              ida1.uniqueName shouldEqual a2.uniqueName
              ida2.uniqueName shouldEqual a1.uniqueName
              Set(idb1.uniqueName, idb2.uniqueName) shouldEqual Set(b1.uniqueName, b2.uniqueName)
            }
          case _ =>
            fail(s"$res is not of type funCall() match { case (a1, b1) => funCall() match { case (a2, b2) => (a1 + a2, b1 || b2) } }")
        }
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
        res match {
          case MatchExpr(funCall, Seq(
                MatchCase(TuplePattern(None, Seq(WildcardPattern(Some(a)), WildcardPattern(Some(b1)))), None,
                  MatchExpr(FunctionInvocation(_, Seq(Variable(ida))), Seq(
                    MatchCase(TuplePattern(None, Seq(WildcardPattern(_), WildcardPattern(Some(b2)))), None,
                      Tuple(Seq(p, Or(Seq(Variable(id1), Variable(id2)))))
                )
              ))))) if ida == a && id1 == b1 && id2 == b2 =>
          case _ =>
            fail(s"$res is not of type funCall() match { case (a, b1) => funCall(a) match { case (c, b2) => (c, b1 || b2) } }")
        }
    }
  }
  
  test("input coverage for booleans should find all of them") { ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withIf = funDef("InputCoverageSuite.withIf")
    val coverage = new InputCoverage(withIf, Set(withIf))
    coverage.result().toSet should equal (Set(Seq(b(true)), Seq(b(false))))
  }
}