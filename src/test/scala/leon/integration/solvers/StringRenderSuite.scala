package leon.integration.solvers


import org.scalatest.FunSuite
import org.scalatest.Matchers
import leon.test.helpers.ExpressionsDSL
import leon.solvers.string.StringSolver
import leon.purescala.Common.FreshIdentifier
import leon.purescala.Common.Identifier
import leon.purescala.Expressions._
import leon.purescala.Definitions._
import leon.purescala.Types._
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
import leon.synthesis.graph.SimpleSearch
import leon.synthesis.graph.AndNode
import leon.synthesis.SearchContext
import leon.synthesis.Synthesizer
import leon.synthesis.SynthesisSettings
import leon.synthesis.RuleApplication
import leon.synthesis.RuleClosed
import leon.evaluators.DefaultEvaluator
import leon.evaluators.AbstractEvaluator
import leon.LeonContext

class StringRenderSuite extends LeonTestSuiteWithProgram with Matchers with ScalaFutures {
  test("Template Generator simple"){ case (ctx: LeonContext, program: Program) =>
    val TTG = new TypedTemplateGenerator(IntegerType) {}
    val e = TTG(hole => Plus(hole, hole))
    val (expr, vars) = e.instantiateWithVars
    vars should have length 2
    expr shouldEqual Plus(Variable(vars(0)), Variable(vars(1)))
    
    val f = TTG.nested(hole => (Minus(hole, expr), vars))
    val (expr2, vars2) = f.instantiateWithVars
    vars2 should have length 3
    vars2(0) shouldEqual vars(0)
    vars2(1) shouldEqual vars(1)
    expr2 shouldEqual Minus(Variable(vars2(2)), expr)
  }
  
  trait withSymbols {
    val x = FreshIdentifier("x", StringType)
    val y = FreshIdentifier("y", StringType)
    val i = FreshIdentifier("i", IntegerType)
    val f = FreshIdentifier("f", FunctionType(Seq(IntegerType), StringType))
    val fd = new FunDef(f, Nil, Seq(ValDef(i)), StringType)
    val fdi = FunctionInvocation(fd.typed, Seq(Variable(i)))
  }
  
  test("toEquations working"){ case (ctx: LeonContext, program: Program) =>
    import StringRender._
    new withSymbols {
      val lhs = RegularStringFormToken(Left("abc"))::RegularStringFormToken(Right(x))::OtherStringFormToken(fdi)::Nil
      val rhs = RegularStringChunk("abcdef")::OtherStringChunk(fdi)::Nil
      val p = toEquations(lhs, rhs)
      p should not be 'empty
      p.get should have length 1
    }
  }
  
  test("toEquations working 2"){ case (ctx: LeonContext, program: Program) =>
    import StringRender._
    new withSymbols {
      val lhs = RegularStringFormToken(Left("abc"))::RegularStringFormToken(Right(x))::OtherStringFormToken(fdi)::RegularStringFormToken(Right(y))::Nil
      val rhs = RegularStringChunk("abcdef")::OtherStringChunk(fdi)::RegularStringChunk("123")::Nil
      val p = toEquations(lhs, rhs)
      p should not be 'empty
      p.get should have length 2
    }
  }
  
  test("toEquations failing"){ case (ctx: LeonContext, program: Program) =>
    import StringRender._
    new withSymbols {
      val lhs = RegularStringFormToken(Left("abc"))::RegularStringFormToken(Right(x))::RegularStringFormToken(Right(y))::Nil
      val rhs = RegularStringChunk("abcdef")::OtherStringChunk(fdi)::RegularStringChunk("123")::Nil
      val p = toEquations(lhs, rhs)
      p should be ('empty)
    }
  }

  def applyStringRenderOn(functionName: String) = {
    val ci = synthesisInfos(functionName)
    val search = new SimpleSearch(ctx, ci, ci.problem, CostModels.default, Some(200))
    val synth = new Synthesizer(ctx, program, ci, SynthesisSettings())
    val orNode = search.g.root
    if (!orNode.isExpanded) {
      val hctx = SearchContext(synth.sctx, synth.ci, orNode, search)
      orNode.expand(hctx)
    }
    val andNodes = orNode.descendants.collect {
      case n: AndNode =>
        n
    }

    val rulesApps = (for ((t, i) <- andNodes.zipWithIndex) yield {
      val status = if (t.isDeadEnd) {
        "closed"
      } else {
        "open"
      }
      t.ri.asString -> i
    }).toMap
    rulesApps should contain key "String conversion"
    
    val rid = rulesApps("String conversion")
    val path = List(rid)
    
    (search.traversePath(path) match {
      case Some(an: AndNode) =>
        val hctx = SearchContext(synth.sctx, synth.ci, an, search)
        an.ri.apply(hctx)
      case _ => throw new Exception("Was not an and node")
    }) match {
      case RuleClosed(solutions) => solutions
      case _ => fail("no solution found")
    }
  }
  
  def getFunctionArguments(functionName: String) = {
    program.lookupFunDef("StringRenderSuite." + functionName) match {
      case Some(fd) => fd.params
      case None => 
        fail("Could not find function " + functionName + " in sources. Other functions:" + program.definedFunctions.map(_.id.name).sorted)
    }
  }
    
  val sources = List("""
    |import leon.lang._
    |import leon.lang.synthesis._
    |import leon.annotation._
    |
    |object StringRenderSuite {
    |  def literalSynthesis(i: Int): String = ??? ensuring { (res: String) => (i, res) passes { case 42 => ":42." } }
    |  
    |}
    """.stripMargin)
  implicit val (ctx, program) = getFixture()
  
  val synthesisInfos = SourceInfo.extractFromProgram(ctx, program).map(si => si.fd.id.name -> si ).toMap
  
  val when = new DefaultEvaluator(ctx, program)
  val when_abstract = new AbstractEvaluator(ctx, program)
  
  test("Literal synthesis"){ case (ctx: LeonContext, program: Program) =>
    val solutions = applyStringRenderOn("literalSynthesis")
    solutions should not be 'empty
    println(solutions.head.term)
    val Seq(arg) = getFunctionArguments("literalSynthesis")
    when.eval(let(arg.id, IntLiteral(156),
        solutions.head.toSimplifiedExpr(ctx, program))).result should equal (Some(StringLiteral(":156.")))
  }
  
  test("String escape synthesis"){ case (ctx: LeonContext, program: Program) =>
    
  }
  
  test("Boolean synthesis"){ case (ctx: LeonContext, program: Program) =>
    
  }
  
  test("Case class synthesis"){ case (ctx: LeonContext, program: Program) =>
    
  }
  
  test("Recursive case class synthesis"){ case (ctx: LeonContext, program: Program) =>
    
  }
  
  test("Out of order synthesis"){ case (ctx: LeonContext, program: Program) =>
    
  }
  
  test("Tuple synthesis"){ case (ctx: LeonContext, program: Program) =>
    
  }
  
  test("Abstract synthesis"){ case (ctx: LeonContext, program: Program) =>
    
  }
  
  test("Use of existing functions"){ case (ctx: LeonContext, program: Program) =>
    
  }
  
  test("Pretty-printing using existing functions"){ case (ctx: LeonContext, program: Program) =>
    // Lists of size 2
  }
}