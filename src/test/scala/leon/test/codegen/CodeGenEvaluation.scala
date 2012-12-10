package leon.test
package codegen

import leon._
import leon.plugin.ExtractionPhase
import leon.codegen.CodeGenPhase
import leon.codegen.CompilationUnit
import leon.purescala.Definitions._

import org.scalatest.FunSuite

import java.io.File

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

  private def mkTest(file : File)(block: Output => Unit) = {
    val fullName = file.getPath()
    val start = fullName.indexOf("regression")
    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }

    test("PureScala program %3d: [%s]".format(nextInt(), displayName)) {
      assert(file.exists && file.isFile && file.canRead,
             "Benchmark [%s] is not a readable file".format(displayName))

      val ctx = LeonContext(
        settings = Settings(
          synthesis = false,
          xlang     = false,
          verify    = false
        ),
        files = List(file),
        reporter = new SilentReporter
      )

      val pipeline = mkPipeline

      val result = pipeline.run(ctx)(file.getPath :: Nil)

      block(Output(result, ctx.reporter))
    }
  }

  private def forFile(f: String)(block : Output => Unit) {
    for (f <- filesInResourceDir("codegen/", _.endsWith(f))) {
      mkTest(f)(block)
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

  forFile("Prog001.scala") { out =>
    assert(out.result.isDefined === true)
    val unit = out.result.get

    val fact = getFunction(unit, "factorial")

    val expr1 = Plus(IntLiteral(5), IntLiteral(42))
    assert(javaEval(unit)(expr1) === IntLiteral(47))


    val expr2 = Plus(FunctionInvocation(fact, Seq(IntLiteral(5))), IntLiteral(42))
    assert(javaEval(unit)(expr2) === IntLiteral(162))

    //Type error
    val expr3 = FunctionInvocation(fact, Seq(BooleanLiteral(false)))
    assert(javaEval(unit)(expr3) != IntLiteral(1), "This should be a type error")
  }

  forFile("Prog002.scala") { out =>
    assert(out.result.isDefined === true)
    val unit = out.result.get

    val ccNil  = getCaseClass(unit, "Nil")
    val ccCons = getCaseClass(unit, "Cons")
    val cons   = getFunction(unit, "conscons")

    val expr1 = FunctionInvocation(cons, Seq(CaseClass(ccNil, Seq())))
    assert(javaEval(unit)(expr1) === CaseClass(ccCons, Seq(IntLiteral(0), CaseClass(ccCons, Seq(IntLiteral(1), CaseClass(ccNil, Seq()))))))
  }

}
