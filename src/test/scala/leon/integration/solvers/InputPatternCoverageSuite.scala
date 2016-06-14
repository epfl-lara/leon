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
import leon.synthesis.disambiguation.InputPatternCoverage
import leon.test.helpers.ExpressionsDSLProgram
import leon.test.helpers.ExpressionsDSLVariables
import leon.purescala.Extractors._
import org.scalatest.PrivateMethodTester.PrivateMethod
import org.scalatest.PrivateMethodTester
import org.scalatest.matchers.Matcher
import org.scalatest.matchers.MatchResult

class InputPatternCoverageSuite extends LeonTestSuiteWithProgram with Matchers with ScalaFutures with ExpressionsDSLProgram with ExpressionsDSLVariables with PrivateMethodTester  {
  override val a = null
  
  override val leonOpts = List[String]("--solvers=smt-cvc4")
  
  val sources = List("""
    |import leon.lang._
    |import leon.collection._
    |import leon.lang.synthesis._
    |import leon.annotation._
    |
    |object InputPatternCoverageSuite {
    |  def dummy = 2
    |  def f(l: List[String]): String    = l match { case Nil() => "[]" case Cons(a, b) => "[" + a + frec(b) }
    |  def frec(l: List[String]): String = l match { case Nil() => ""   case Cons(a, b) => "," + a + frec(b) }
    |  
    |  // Slightly different version of f with one inversion not caught by just covering examples.
    |  def g(l: List[String]): String    = l match { case Nil() => "[]" case Cons(a, b) => "[" + a + grec(b) }
    |  def grec(l: List[String]): String = l match { case Nil() => ""   case Cons(a, b) => "," + grec(b) + a }
    |  
    |  // Testing  buildMarkableValue
    |  abstract class A
    |  case class B() extends A
    |  case class C(i: String) extends A
    |  
    |  abstract class AA
    |  case class E(i: Boolean) extends AA
    |  case class F(a: A) extends AA
    |  
    |  abstract class L
    |  case class Co(b: Boolean, l: L) extends L
    |  case class Ni() extends L
    |  
    |  def h(a: A, l: L): String = hA(a) + hL(l)
    |  def hA(a: A): String = a match { case B() => "b" case C(i) => i }
    |  def hL(l: L): String=  l match { case Co(b, tail) => b.toString + "," + hL(tail) case Ni() => "]" }
    |}
    |object CornerExamples {
    |  abstract class A
    |  case class R(a: A) extends A
    |  case class L(a: A) extends A
    |  case class C(a: A) extends A
    |  case class E() extends A
    |  
    |  def f(a: A): String = a match {
    |    case R(a) => f(a) + "."
    |    case L(a) => "." + f(a)
    |    case C(a) => f(a)
    |    case E() => "A"
    |  }
    |  def h(a: List[A]): String = a match{
    |    case Nil() => ""
    |    case Cons(a, t) => f(a) + h(t)
    |  }
    |}""".stripMargin)
    
  
  def haveOneWhich[T](pred: T => Boolean, predStr: String = "")(implicit m: Manifest[Iterable[T]]) =  Matcher { (left: Iterable[T]) =>  
    MatchResult( 
      left exists pred,
      s"No element $predStr among ${left.mkString(", ")}",
      s"All elements of ${left.mkString(", ")} $predStr")
  }
  
  def eval(f: FunDef)(e: Seq[Expr])(implicit ctx: LeonContext, program: Program): Expr = {
    val d = new DefaultEvaluator(ctx, program)
    d.eval(functionInvocation(f, e)).result.get
  }
  
  test("InputPatternCoverage should expand covering examples."){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    val f = funDef("InputPatternCoverageSuite.f")
    val reccoverage = new InputPatternCoverage(f.typed)
    reccoverage.result() should have size 3
  }
  
  test("InputPatternCoverage on multiple arguments should work"){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    val h = funDef("InputPatternCoverageSuite.h")
    val reccoverage = new InputPatternCoverage(h.typed)
    reccoverage.result() should have size 4
  }
  
  test("InputPatternCoverage should exhaustively find arguments"){ ctxprogram =>
    implicit val (c, p) = ctxprogram
    
    val h = funDef("CornerExamples.h")
    
    val reccoverage = new InputPatternCoverage(h.typed)
    reccoverage.result() should have size 5
  }
}