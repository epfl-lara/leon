package leon.test
package codegen

import leon._
import leon.plugin.{TemporaryInputPhase, ExtractionPhase}
import leon.codegen.CompilationUnit
import leon.purescala.Definitions._
import leon.purescala.TypeTrees.TypeErrorException

import org.scalatest.FunSuite

import TestUtils._

class CodeGenEvaluation extends FunSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }

  object CodeTestPhase extends LeonPhase[Program,Option[CompilationUnit]] {
    val name = "CodeGen"
    val description = "Compiles a Leon program into Java methods"

    def run(ctx : LeonContext)(p : Program) : Option[CompilationUnit] = {
      CompilationUnit.compileProgram(p)
    }
  }

  private case class Output(result : Option[CompilationUnit], reporter : Reporter)

  private def mkPipeline : Pipeline[List[String], Option[CompilationUnit]] =
    ExtractionPhase andThen CodeTestPhase

  private def forProgram(name: String)(content: String)(block: Output => Unit) = {
    test("PureScala program %3d: [%s]".format(nextInt(), name)) {

      val ctx = LeonContext(
        settings = Settings(
          synthesis = false,
          xlang     = false,
          verify    = false
        ),
        files = List(),
        reporter = new SilentReporter
      )

      val pipeline = TemporaryInputPhase andThen ExtractionPhase andThen CodeTestPhase

      val result = pipeline.run(ctx)((content, Nil))

      block(Output(result, ctx.reporter))
    }
  }

  import purescala.Trees._

  def javaEval(unit: CompilationUnit)(ex: Expr): Expr = {
    val cp = unit.compileExpression(ex, Seq())
    cp.eval(Seq())
  }

  def getFunction(unit: CompilationUnit, name: String): FunDef = {
    unit.program.definedFunctions.find(_.id.toString == name) match {
      case Some(fd) =>
        fd
      case _ =>
        throw new AssertionError("Could not find any function named '"+name+"'")
    }
  }

  def getCaseClass(unit: CompilationUnit, name: String): CaseClassDef = {
    unit.program.mainObject.caseClassDef(name)
  }

  forProgram("Simple Evaluation")(
    """
object Prog001 {
  def fortyTwo() = 42

  def plus(x : Int, y : Int) = x + y

  def double(x : Int) : Int = {
    val a = x
    a + a
  }

  def implies(a : Boolean, b : Boolean) : Boolean = !a || b

  def abs(x : Int) : Int = {
    if(x < 0) -x else x
  }

  def factorial(i : Int) : Int = if(i <= 1) 1 else (i * factorial(i - 1))
}
    """
  ){ out =>
    assert(out.result.isDefined === true)
    val unit = out.result.get

    val fact = getFunction(unit, "factorial")

    val expr1 = Plus(IntLiteral(5), IntLiteral(42))
    assert(javaEval(unit)(expr1) === IntLiteral(47))


    val expr2 = Plus(FunctionInvocation(fact, Seq(IntLiteral(5))), IntLiteral(42))
    assert(javaEval(unit)(expr2) === IntLiteral(162))

    //Type error
    intercept[TypeErrorException] {
      val expr3 = FunctionInvocation(fact, Seq(BooleanLiteral(false)))
      assert(javaEval(unit)(expr3) != IntLiteral(1), "This should be a type error")
    }
  }

  forProgram("Case Classes Evaluation")(
    """
object Prog002 {
  sealed abstract class List
  case class Nil() extends List
  case class Cons(head : Int, tail : List) extends List

  def isNil(l : List) : Boolean = {
    l == Nil()
  }

  def size(l : List) : Int = l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }

  def conscons(l: List): List = Cons(0, Cons(1, l))
}
    """
  ){ out =>
    assert(out.result.isDefined === true)
    val unit = out.result.get

    val ccNil  = getCaseClass(unit, "Nil")
    val ccCons = getCaseClass(unit, "Cons")
    val cons   = getFunction(unit, "conscons")

    val expr1 = FunctionInvocation(cons, Seq(CaseClass(ccNil, Seq())))
    assert(javaEval(unit)(expr1) === CaseClass(ccCons, Seq(IntLiteral(0), CaseClass(ccCons, Seq(IntLiteral(1), CaseClass(ccNil, Seq()))))))
  }

  forProgram("Set Evaluation")(
    """
object Sets {
  def s0() : Set[Int] = Set()
  def s1() : Set[Int] = Set(1, 2, 3)
  def s2() : Set[Int] = Set(2, 4, 6)
  def s3() : Set[Int] = s1() ++ s2()
  def s4() : Set[Int] = s2() ++ s1()
  def s5() : Set[Int] = s1() ** s2()
  def s6() : Set[Int] = s2() ** s1()
  def s7() : Set[Int] = s1() -- s2()
  def s8() : Set[Int] = s2() -- s1()
}
    """
  ){ out =>
    assert(out.result.isDefined === true)
    val unit = out.result.get

    def asIntSet(e : Expr) : Option[Set[Int]] = e match {
      case FiniteSet(es) =>
        val ois = es.map(_ match {
          case IntLiteral(v) => Some(v)
          case _ => None
        })
        if(ois.forall(_.isDefined))
          Some(ois.map(_.get).toSet)
        else
          None
      case _ => None
    }

    def eval(f : String) : Option[Set[Int]] = asIntSet(javaEval(unit)(FunctionInvocation(getFunction(unit, f), Seq())))

    assert(eval("s0") === Some(Set.empty[Int]))
    assert(eval("s1") === Some(Set(1, 2, 3)))
    assert(eval("s2") === Some(Set(2, 4, 6)))
    assert(eval("s3") === Some(Set(1, 2, 3, 4, 6)))
    assert(eval("s4") === Some(Set(2, 4, 6, 1, 3)))
    assert(eval("s5") === Some(Set(2)))
    assert(eval("s6") === Some(Set(2)))
    assert(eval("s7") === Some(Set(1, 3)))
    assert(eval("s8") === Some(Set(4, 6)))
  }
}
