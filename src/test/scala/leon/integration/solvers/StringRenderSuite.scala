package leon
package integration
package solvers

import leon.test.LeonTestSuiteWithProgram

import leon.purescala.Common.FreshIdentifier
import leon.purescala.Expressions._
import leon.purescala.Definitions._
import leon.purescala.DefOps
import leon.purescala.ExprOps
import leon.purescala.Types._
import leon.purescala.Constructors._

import leon.synthesis._
import leon.synthesis.rules.{StringRender, TypedTemplateGenerator}
import leon.synthesis.strategies.CostBasedStrategy
import leon.synthesis.graph.AndNode

import leon.evaluators._

import org.scalatest.concurrent.ScalaFutures
import org.scalatest.Matchers
import scala.language.implicitConversions

class StringRenderSuite extends LeonTestSuiteWithProgram with Matchers with ScalaFutures {

  override val leonOpts = List("--solvers=smt-cvc4")

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
    val search = new Search(ctx, ci, ci.problem, new CostBasedStrategy(ctx, CostModels.default))
    val synth = new Synthesizer(ctx, program, ci, SynthesisSettings(rules = Seq(StringRender)))
    val orNode = search.g.root
    if (!orNode.isExpanded) {
      val hctx = new SearchContext(synth.sctx, synth.ci.source, orNode, search)
      orNode.expand(hctx)
    }
    val andNodes = orNode.descendants.collect {
      case n: AndNode =>
        n
    }

    val rulesApps = (for ((t, i) <- andNodes.zipWithIndex) yield {
      t.ri.asString -> i
    }).toMap
    rulesApps should contain key "String conversion"
    
    val rid = rulesApps("String conversion")
    val path = List(rid)
    
    val solutions = (search.traversePath(path) match {
      case Some(an: AndNode) =>
        val hctx = new SearchContext(synth.sctx, synth.ci.source, an, search)
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
    val (newProgram2, _, _, _) = DefOps.replaceFunDefs(newProgram)({ fd =>
      if(fd == ci.fd) Some(newFd) else None
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
    |  case class Dummy2(s: String)
    |  def dummy2ToString(d: Dummy2): String = "<" + d.s + ">"
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
    |  // Handling one rendering function at a time.
    |  case class BConfig(flags: BList[Dummy])
    |  def bConfigToString(b: BConfig): String = ???[String] ensuring
    |  { (res: String) => (b, res) passes { case BConfig(BNil()) => "Config" + bListToString[Dummy](BNil(), (x: Dummy) => dummyToString(x)) } }
    |  
    |  def customListToString[T](l: List[T], f: T => String): String = ???[String] ensuring
    |  { (res: String) => (l, res) passes { case _ if false => "" } }
    |  
    |  // Handling multiple rendering functions at the same time.
    |  case class DConfig(dums: List[Dummy], dums2: List[Dummy2])
    |  def dConfigToString(dc: DConfig): String = ???[String] ensuring
    |  { (res: String) => (dc, res) passes {
    |    case DConfig(Nil(), Nil()) => 
    |    "Solution:\n  " + customListToString[Dummy](List[Dummy](), (x : Dummy) => dummyToString(x)) + "\n  " + customListToString[Dummy2](List[Dummy2](), (x: Dummy2) => dummy2ToString(x)) } }
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

  val synthesisInfos = SourceInfo.extractFromProgram(ctx, program).map(si => si.fd.id.name -> si).toMap

  def synthesizeAndTest(functionName: String, tests: (Seq[Expr], String)*) {
    val (fd, program) = applyStringRenderOn(functionName)
    val when = new DefaultEvaluator(ctx, program)
    for((in, out) <- tests) {
      val expr = functionInvocation(fd, in)
      when.eval(expr) match {
        case EvaluationResults.Successful(value) => value shouldEqual StringLiteral(out)
        case EvaluationResults.EvaluatorError(msg) => fail(/*program + "\n" + */msg)
        case EvaluationResults.RuntimeError(msg) => fail(/*program + "\n" + */"Runtime: " + msg)
      }
    }
  }
  def synthesizeAndAbstractTest(functionName: String)(tests: (FunDef, Program) => Seq[(Seq[Expr], Expr)]) {
    val (fd, program) = applyStringRenderOn(functionName)
    val when_abstract = new AbstractEvaluator(ctx, program)
    for((in, out) <- tests(fd, program)) {
      val expr = functionInvocation(fd, in)
      when_abstract.eval(expr) match {
        case EvaluationResults.Successful(value) => val m = ExprOps.canBeHomomorphic(value._1, out)
          assert(m.nonEmpty, value._1 + " was not homomorphic with " + out)
        case EvaluationResults.EvaluatorError(msg) => fail(/*program + "\n" + */msg)
        case EvaluationResults.RuntimeError(msg) => fail(/*program + "\n" + */"Runtime: " + msg)
      }
    }
  }
  abstract class CCBuilder(ccName: String, prefix: String = "StringRenderSuite.")(implicit program: Program) {
    val caseClassName = prefix + ccName
    def getType: TypeTree = program.lookupCaseClass(caseClassName).get.typed
    def apply(s: Expr*): CaseClass = {
      CaseClass(program.lookupCaseClass(caseClassName).get.typed, s.toSeq)
    }
    def apply(s: String): CaseClass = this.apply(StringLiteral(s))
  }
  abstract class ParamCCBuilder(caseClassName: String, prefix: String = "StringRenderSuite.")(implicit program: Program) {
    def apply(types: TypeTree*)(s: Expr*): CaseClass = {
      CaseClass(program.lookupCaseClass(prefix+caseClassName).get.typed(types),
          s.toSeq)
    }
  }
  def method(fName: String)(implicit program: Program) = {
    program.lookupFunDef("StringRenderSuite." + fName).get
  }
  abstract class paramMethod(fName: String)(implicit program: Program) {
    val fd = program.lookupFunDef("StringRenderSuite." + fName).get
    def apply(types: TypeTree*)(args: Expr*) =
      FunctionInvocation(fd.typed(types), args)
  }

  // Mimics the file above, allows construction of expressions.
  case class Constructors(program: Program) {
    implicit val p = program
    implicit def CCBuilderToType(c: CCBuilder): TypeTree = c.getType
    object Knot extends CCBuilder("Knot")
    object Bud extends CCBuilder("Bud")
    object Dummy extends CCBuilder("Dummy")
    object Dummy2 extends CCBuilder("Dummy2")
    object Cons extends ParamCCBuilder("Cons", "leon.collection.")
    object Nil extends ParamCCBuilder("Nil", "leon.collection.")
    object List {
      def apply(types: TypeTree*)(elems: Expr*): CaseClass = {
        elems.toList match {
          case collection.immutable.Nil => Nil(types: _*)()
          case a::b => Cons(types: _*)(a, List(types: _*)(b: _*))
        }
      }
    }
    
    object BCons extends ParamCCBuilder("BCons")
    object BNil extends ParamCCBuilder("BNil")
    object BList {
      def apply(types: TypeTree*)(elems: Expr*): CaseClass = {
        elems.toList match {
          case collection.immutable.Nil => BNil(types: _*)()
          case a::b => BCons(types: _*)(a, BList(types: _*)(b: _*))
        }
      }
      def helper(types: TypeTree*)(elems: (Expr, Expr)*): CaseClass = {
        this.apply(types: _*)(elems.map(x => tupleWrap(Seq(x._1, x._2))): _*)
      }
    }
    object Config extends CCBuilder("Config") {
      def apply(i: Int, b: (Int, String)): CaseClass =
        this.apply(InfiniteIntegerLiteral(i), tupleWrap(Seq(IntLiteral(b._1), StringLiteral(b._2))))
    }
    object BConfig extends CCBuilder("BConfig")
    object DConfig extends CCBuilder("DConfig")
    lazy val dummyToString = method("dummyToString")
    lazy val dummy2ToString = method("dummy2ToString")
    lazy val bListToString = method("bListToString")
    object customListToString extends paramMethod("customListToString")
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
  
  test("Case class synthesis"){ case (ctx: LeonContext, program: Program) =>
    val c = Constructors(program); import c._
    StringRender.enforceDefaultStringMethodsIfAvailable = false
    synthesizeAndTest("configToString",
        Seq(Config(4, (5, "foo"))) -> "4: 5 -> foo")
  }
  
  test("Out of order synthesis"){ case (ctx: LeonContext, program: Program) =>
    val c = Constructors(program); import c._
    StringRender.enforceDefaultStringMethodsIfAvailable = false
    synthesizeAndTest("configToString2",
        Seq(Config(4, (5, "foo"))) -> "foo: 4 -> 5")
  }
  
  test("Recursive case class synthesis"){ case (ctx: LeonContext, program: Program) =>
    val c = Constructors(program); import c._
    synthesizeAndTest("treeToString",
        Seq(Knot(Knot(Bud("aa"), Bud("bb")), Knot(Bud("mm"), Bud("nn")))) ->
        "<<aaYbb>Y<mmYnn>>")
  }
  
  test("Abstract synthesis"){ case (ctx: LeonContext, program: Program) =>
    val c = Constructors(program); import c._
    val d = FreshIdentifier("d", Dummy)

    synthesizeAndTest("bListToString",
        Seq(BList.helper(Dummy)(
              (Dummy("a"), Dummy("b")),
              (Dummy("c"), Dummy("d"))),
            Lambda(Seq(ValDef(d)), FunctionInvocation(dummyToString.typed, Seq(Variable(d)))))
            ->
        "[{a}-{b}, {c}-{d}]")
    
  }
  
  
  test("Pretty-printing using inferred not yet defined functions in argument"){ case (ctx: LeonContext, program: Program) =>
    StringRender.enforceDefaultStringMethodsIfAvailable = true
    synthesizeAndAbstractTest("bConfigToString"){ (fd: FunDef, program: Program) =>
      val c = Constructors(program); import c._
      val arg = BList.helper(Dummy)((Dummy("a"), Dummy("b")))
      val d = FreshIdentifier("d", Dummy)
      val lambdaDummyToString = Lambda(Seq(ValDef(d)), FunctionInvocation(dummyToString.typed, Seq(Variable(d))))
      val listDummyToString = functionInvocation(bListToString, Seq(arg, lambdaDummyToString))
      Seq(Seq(BConfig(arg)) ->
      StringConcat(StringLiteral("Config"), listDummyToString))
    }
  }
  
  test("Pretty-printing using an existing not yet defined parametrized function") { case (ctx: LeonContext, program: Program) =>
    StringRender.enforceDefaultStringMethodsIfAvailable = true
    
    synthesizeAndAbstractTest("dConfigToString"){ (fd: FunDef, program: Program) =>
      val c = Constructors(program); import c._
      
      val listDummy1 = c.List(Dummy)(Dummy("a"), Dummy("b"), Dummy("c"))
      val listDummy2 = c.List(Dummy2)(Dummy2("1"), Dummy2("2"))
      val arg = DConfig(listDummy1, listDummy2)
      
      val d = FreshIdentifier("d", Dummy)
      val lambdaDummyToString = Lambda(Seq(ValDef(d)), FunctionInvocation(dummyToString.typed, Seq(Variable(d))))
      val d2 = FreshIdentifier("d2", Dummy2)
      val lambdaDummy2ToString = Lambda(Seq(ValDef(d2)), FunctionInvocation(dummy2ToString.typed, Seq(Variable(d2))))
          
      Seq(Seq(arg) ->
      StringConcat(StringConcat(StringConcat(
          StringLiteral("Solution:\n  "),
          customListToString(Dummy)(listDummy1, lambdaDummyToString)),
          StringLiteral("\n  ")),
          customListToString(Dummy2)(listDummy2, lambdaDummy2ToString)))
    }
  }
}
