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
import leon.synthesis.graph.SimpleSearch
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

  def applyStringRenderOn(functionName: String): (FunDef, Program) = {
    val ci = synthesisInfos(functionName)
    val search = new SimpleSearch(ctx, ci, ci.problem, CostModels.default, Some(200))
    val synth = new Synthesizer(ctx, program, ci, SynthesisSettings(rules = Seq(StringRender)))
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
    
    val solutions = (search.traversePath(path) match {
      case Some(an: AndNode) =>
        val hctx = SearchContext(synth.sctx, synth.ci, an, search)
        an.ri.apply(hctx)
      case _ => throw new Exception("Was not an and node")
    }) match {
      case RuleClosed(solutions) => solutions
      case _ => fail("no solution found")
    }
    solutions should not be 'empty
    val newProgram = DefOps.addFunDefs(synth.program, solutions.head.defs, synth.sctx.functionContext)
    val newFd = ci.fd.duplicate()
    newFd.body = Some(solutions.head.term)
    val (newProgram2, _) = DefOps.replaceFunDefs(newProgram)({ fd =>
      if(fd == ci.fd) {
        Some(newFd)
      } else None
    }, { (fi: FunctionInvocation, fd: FunDef) =>
      Some(FunctionInvocation(fd.typed, fi.args))
    })
    (newFd, newProgram2)
  }
  
  def getFunctionArguments(functionName: String) = {
    program.lookupFunDef("StringRenderSuite." + functionName) match {
      case Some(fd) => fd.params
      case None => 
        fail("Could not find function " + functionName + " in sources. Other functions:" + program.definedFunctions.map(_.id.name).sorted)
    }
  }
  
  implicit class StringUtils(s: String) {
    def replaceByExample: String = 
      s.replaceAll("\\((\\w+):(.*) by example", "\\($1:$2 ensuring { (res: String) => ($1, res) passes { case _ if false => \"\" } }")
  }
    
  val sources = List("""
    |import leon.lang._
    |import leon.collection._
    |import leon.lang.synthesis._
    |import leon.annotation._
    |
    |object StringRenderSuite {
    |  def literalSynthesis(i: Int): String = ??? ensuring { (res: String) => (i, res) passes { case 42 => ":42." } }
    |  
    |  def booleanSynthesis(b: Boolean): String = ??? ensuring { (res: String) => (b, res) passes { case true => "yes" case false => "no" } }
    |  def booleanSynthesis2(b: Boolean): String = ??? ensuring { (res: String) => (b, res) passes { case true => "B: true" } }
    |  //def stringEscape(s: String): String = ??? ensuring { (res: String) => (s, res) passes { case "\n" => "done...\\n" } }
    |  
    |  case class Dummy(s: String)
    |  def dummyToString(d: Dummy): String = "{" + d.s + "}"
    |  
    |  case class Config(i: BigInt, t: (Int, String))
    |  
    |  def configToString(c: Config): String = ??? ensuring { (res: String) => (c, res) passes { case Config(BigInt(1), (2, "3")) => "1: 2 -> 3" } }
    |  def configToString2(c: Config): String = ??? ensuring { (res: String) => (c, res) passes { case Config(BigInt(1), (2, "3")) => "3: 1 -> 2" } }
    |  
    |  sealed abstract class Tree
    |  case class Knot(left: Tree, right: Tree) extends Tree
    |  case class Bud(v: String) extends Tree
    |  
    |  def treeToString(t: Tree): String = ???[String] ensuring {
    |    (res : String) => (t, res) passes {
    |    case Knot(Knot(Bud("17"), Bud("14")), Bud("23")) =>
    |      "<<17Y14>Y23>"
    |    case Bud("foo") =>
    |      "foo"
    |    case Knot(Bud("foo"), Bud("foo")) =>
    |      "<fooYfoo>"
    |    case Knot(Bud("foo"), Knot(Bud("bar"), Bud("foo"))) =>
    |      "<fooY<barYfoo>>"
    |    }
    |  }
    |  
    |  sealed abstract class BList[T]
    |  case class BCons[T](head: (T, T), tail: BList[T]) extends BList[T]
    |  case class BNil[T]() extends BList[T]
    |  
    |  def bListToString[T](b: BList[T], f: T => String) = ???[String] ensuring
    |  { (res: String) => (b, res) passes { case BNil() => "[]" case BCons(a, BCons(b, BCons(c, BNil()))) => "[" + f(a._1) + "-" + f(a._2) + ", " + f(b._1) + "-" + f(b._2) + ", " + f(c._1) + "-" + f(c._2) + "]" }}
    |  
    |  case class Node(tag: String, l: List[Edge])
    |  case class Edge(start: Node, end: Node)
    |  
    |  def nodeToString(n: Node): String = ??? by example
    |  def edgeToString(e: Edge): String = ??? by example
    |  def listEdgeToString(l: List[Edge]): String = ??? by example
    |}
    """.stripMargin.replaceByExample)
  implicit val (ctx, program) = getFixture()
  
  val synthesisInfos = SourceInfo.extractFromProgram(ctx, program).map(si => si.fd.id.name -> si ).toMap

  def synthesizeAndTest(functionName: String, tests: (Seq[Expr], String)*) {
    val (fd, program) = applyStringRenderOn(functionName)
    val when = new DefaultEvaluator(ctx, program)
    val when_abstract = new AbstractEvaluator(ctx, program)
    val args = getFunctionArguments(functionName)
    for((in, out) <- tests) {
      val expr = functionInvocation(fd, in)
      when.eval(expr) match {
        case EvaluationResults.Successful(value) => value shouldEqual StringLiteral(out)
        case EvaluationResults.EvaluatorError(msg) => fail(/*program + "\n" + */msg)
        case EvaluationResults.RuntimeError(msg) => fail(/*program + "\n" + */"Runtime: " + msg)
      }
    }
  }
  
  test("Literal synthesis"){ case (ctx: LeonContext, program: Program) =>
    synthesizeAndTest("literalSynthesis",
        Seq(IntLiteral(156)) -> ":156.",
        Seq(IntLiteral(-5)) -> ":-5.")
  }
  
  test("boolean Synthesis"){ case (ctx: LeonContext, program: Program) =>
    synthesizeAndTest("booleanSynthesis",
        Seq(BooleanLiteral(true)) -> "yes",
        Seq(BooleanLiteral(false)) -> "no")
  }
  
  test("Boolean synthesis 2"){ case (ctx: LeonContext, program: Program) =>
    synthesizeAndTest("booleanSynthesis2",
        Seq(BooleanLiteral(true)) -> "B: true",
        Seq(BooleanLiteral(false)) -> "B: false")
  }
  
  /*test("String escape synthesis"){ case (ctx: LeonContext, program: Program) =>
    synthesizeAndTest("stringEscape",
        Seq(StringLiteral("abc")) -> "done...abc",
        Seq(StringLiteral("\t")) -> "done...\\t")
        
  }*/
  case class ConfigBuilder(program: Program) {
    def apply(i: Int, b: (Int, String)): CaseClass = {
      CaseClass(program.lookupCaseClass("StringRenderSuite.Config").get.typed,
          Seq(InfiniteIntegerLiteral(i), tupleWrap(Seq(IntLiteral(b._1), StringLiteral(b._2)))))
    }
  }
  StringRender.enforceDefaultStringMethodsIfAvailable = false
  test("Case class synthesis"){ case (ctx: LeonContext, program: Program) =>
    val Config = ConfigBuilder(program)
    
    synthesizeAndTest("configToString",
        Seq(Config(4, (5, "foo"))) -> "4: 5 -> foo")
  }
  
  test("Out of order synthesis"){ case (ctx: LeonContext, program: Program) =>
    val Config = ConfigBuilder(program)
    
    synthesizeAndTest("configToString2",
        Seq(Config(4, (5, "foo"))) -> "foo: 4 -> 5")
  }
  class TreeBuilder(program: Program) {
    object Knot {
      def apply(left: Expr, right: Expr): CaseClass = {
        CaseClass(program.lookupCaseClass("StringRenderSuite.Knot").get.typed,
            Seq(left, right))
      }
    }
    object Bud {
      def apply(s: String): CaseClass = {
        CaseClass(program.lookupCaseClass("StringRenderSuite.Bud").get.typed,
            Seq(StringLiteral(s)))
      }
    }
  }
  
  test("Recursive case class synthesis"){ case (ctx: LeonContext, program: Program) =>
    val tb = new TreeBuilder(program)
    import tb._
    synthesizeAndTest("treeToString",
        Seq(Knot(Knot(Bud("aa"), Bud("bb")), Knot(Bud("mm"), Bud("nn")))) ->
        "<<aaYbb>Y<mmYnn>>")
  }
  
  class DummyBuilder(program: Program) {
    object Dummy {
      def getType: TypeTree = program.lookupCaseClass("StringRenderSuite.Dummy").get.typed
      def apply(s: String): CaseClass = {
        CaseClass(program.lookupCaseClass("StringRenderSuite.Dummy").get.typed,
            Seq(StringLiteral(s)))
      }
    }
  }
  
  class BListBuilder(program: Program) {
    object Cons {
      def apply(types: Seq[TypeTree])(left: Expr, right: Expr): CaseClass = {
        CaseClass(program.lookupCaseClass("StringRenderSuite.BCons").get.typed(types),
            Seq(left, right))
      }
    }
    object Nil {
      def apply(types: Seq[TypeTree]): CaseClass = {
        CaseClass(program.lookupCaseClass("StringRenderSuite.BNil").get.typed(types),
            Seq())
      }
    }
  }
  test("Abstract synthesis"){ case (ctx: LeonContext, program: Program) =>
    val db = new DummyBuilder(program)
    import db._
    val DT = Seq(Dummy.getType)
    val bb = new BListBuilder(program)
    import bb._
    val d = FreshIdentifier("d", Dummy.getType)
    val dummyToString = program.lookupFunDef("StringRenderSuite.dummyToString").get
    
    synthesizeAndTest("bListToString",
        Seq(Cons(DT)(tupleWrap(Seq(Dummy("a"), Dummy("b"))),
            Cons(DT)(tupleWrap(Seq(Dummy("c"), Dummy("d"))),
            Nil(DT))),
            Lambda(Seq(ValDef(d)), FunctionInvocation(dummyToString.typed, Seq(Variable(d)))))
            ->
        "[{a}-{b}, {c}-{d}]")
    
  }
  
  test("Use of existing functions"){ case (ctx: LeonContext, program: Program) =>
    
  }
  
  test("Pretty-printing using existing functions"){ case (ctx: LeonContext, program: Program) =>
    // Lists of size 2
  }
}