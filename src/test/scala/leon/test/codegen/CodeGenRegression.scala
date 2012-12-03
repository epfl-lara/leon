package leon.test
package codegen

import leon._
import leon.plugin.ExtractionPhase
import leon.codegen.CodeGenPhase
import leon.codegen.CompilationResult

import org.scalatest.FunSuite

import java.io.File

import TestUtils._

class CodeGenRegression extends FunSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }

  private case class Output(result : CompilationResult, reporter : Reporter)

  private def mkPipeline : Pipeline[List[String],CompilationResult] =
    ExtractionPhase andThen CodeGenPhase

  private def mkTest(file : File)(block: Output=>Unit) = {
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

  private def forEachFileIn(cat : String)(block : Output=>Unit) {
    val fs = filesInResourceDir(
      "regression/codegen/" + cat,
      _.endsWith(".scala"))

    for(f <- fs) {
      mkTest(f)(block)
    }
  }
  
  forEachFileIn("purescala") { output =>
    val Output(result, reporter) = output
    assert(result.successful, "Compilation should be successful.")
    assert(reporter.errorCount === 0)
    assert(reporter.warningCount === 0)
  }
}
