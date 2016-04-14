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
    |  def withIfInIf(cond: Boolean) = {
    |    if(if(cond) false else true) {
    |      1
    |    } else {
    |      2
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
    coverage.wrapBranch((simpleExpr, Seq(p.id, q.id))) should equal ((simpleExpr, Seq(p.id, q.id)))
    val (covered, ids) = coverage.wrapBranch((simpleExpr, Seq()))
    ids should have size 1
    covered should equal (Tuple(Seq(simpleExpr, Variable(ids.head))))
  }
  
  test("If-coverage should work"){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withIf = funDef("InputCoverageSuite.withIf")
    val coverage = new InputCoverage(withIf, Set(withIf))
    val expr = withIf.body.get
    
    val (res, ids) = coverage.markBranches(expr)
    ids should have size 2
    expr match {
      case IfExpr(cond, thenn, elze) =>
        res should equal (IfExpr(cond, Tuple(Seq(thenn, Variable(ids(0)))), Tuple(Seq(elze, Variable(ids(1))))))
      case _ => fail(s"$expr is not an IfExpr")
    }
  }
  
  test("If-cond-coverage should work"){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withIfInIf = funDef("InputCoverageSuite.withIfInIf")
    val coverage = new InputCoverage(withIfInIf, Set(withIfInIf))
    val expr = withIfInIf.body.get
    
    val (res, ids) = coverage.markBranches(expr)
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
  
  test("fundef combination-coverage should work"){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withCoveredFun1 = funDef("InputCoverageSuite.withCoveredFun1")
    val withCoveredFun2 = funDef("InputCoverageSuite.withCoveredFun2")
    val coverage = new InputCoverage(withCoveredFun1, Set(withCoveredFun1, withCoveredFun2))
    val expr = withCoveredFun1.body.get
    
    val (res, ids) = coverage.markBranches(expr)
    ids should have size 2
    
    res match {
      case MatchExpr(funCall, Seq(
            MatchCase(TuplePattern(None, Seq(WildcardPattern(Some(a1)), WildcardPattern(Some(b1)))), None,
              MatchExpr(funCall2, Seq(
                MatchCase(TuplePattern(None, Seq(WildcardPattern(Some(a2)), WildcardPattern(Some(b2)))), None,
                  Tuple(Seq(BVPlus(Variable(ida1), Variable(ida2)), Or(Seq(Variable(idb1), Variable(idb2)))))
            )
          ))))) =>
        withClue(res.toString) {
          ida1 shouldEqual a1
          ida2 shouldEqual a2
          Set(idb1.uniqueName, idb2.uniqueName) shouldEqual Set(b1.uniqueName, b2.uniqueName)
        }
      case _ =>
        fail(s"$res is not of type funCall() match { case (a1, b1) => funCall() match { case (a2, b2) => (a1 + a2, b1 || b2) } }")
    }
  }
  
  test("fundef composition-coverage should work"){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    val withCoveredFun2 = funDef("InputCoverageSuite.withCoveredFun2")
    val withCoveredFun3 = funDef("InputCoverageSuite.withCoveredFun3")
    val coverage = new InputCoverage(withCoveredFun3, Set(withCoveredFun3, withCoveredFun2))
    val expr = withCoveredFun3.body.get
    
    val (res, ids) = coverage.markBranches(expr)
    ids should have size 2
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