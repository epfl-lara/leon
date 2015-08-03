/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.verification

import leon._
import leon.test._
import leon.verification.VCStatus._

import leon.verification.VerificationReport
import leon.purescala.Definitions.Program
import leon.frontends.scalac.ExtractionPhase
import leon.utils.PreprocessingPhase

import org.scalatest.{Reporter => TestReporter, _}

// If you add another regression test, make sure it contains one object whose name matches the file name
// This is because we compile all tests from each folder separately.
trait VerificationSuite extends LeonTestSuite {

  val optionVariants: List[List[String]]
  val testDir: String

  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }
  private[verification] case class Output(report : VerificationReport, reporter : Reporter)
 
  val pipeFront: Pipeline[Program, Program]
  val pipeBack : Pipeline[Program, VerificationReport]

  private def mkTest(files: List[String], cat: String)(block: Output=>Unit) = {
    val extraction =
      ExtractionPhase andThen
      PreprocessingPhase andThen
      pipeFront

    val ctx = createLeonContext(files:_*)

    try {
      val ast = extraction.run(ctx)(files)
      val programs = {
        val (user, lib) = ast.units partition { _.isMainUnit }
        user map { u => (u.id, Program(u :: lib)) }
      }
      for ((id, p) <- programs; options <- optionVariants) {
        test(f"${nextInt()}%3d: ${id.name} ${options.mkString(" ")}") {
          val ctx = createLeonContext(options: _*)
          val report = pipeBack.run(ctx)(p)
          block(Output(report, ctx.reporter))
        }
      }
    } catch {
      case _: LeonFatalError =>
        ctx.reporter match {
          case sr: TestSilentReporter =>
            println("Unnexpected Fatal error:")
            for (e <- sr.lastErrors) {
              println(" "+e)
            }
          case _ =>
        }
        test("Compilation of test files in " + testDir + cat)(fail("Failed to compile"))
    }
  }

  private[verification] def forEachFileIn(cat : String)(block : Output=>Unit) {
    val fs = filesInResourceDir( testDir + cat, _.endsWith(".scala")).toList

    fs foreach { file => 
      assert(file.exists && file.isFile && file.canRead,
        s"Benchmark ${file.getName} is not a readable file")
    }

    val files = fs map { _.getPath }

    mkTest(files, cat)(block)
  }

  override def run(testName: Option[String], args: Args): Status = {
    forEachFileIn("valid") { output =>
      val Output(report, reporter) = output
      for ((vc, vr) <- report.vrs if (vr.isInvalid)) {
        fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      }
      for ((vc, vr) <- report.vrs if (vr.isInconclusive)) {
        fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
      }
      reporter.terminateIfError()
    }

    forEachFileIn("invalid") { output =>
      val Output(report, reporter) = output
      assert(report.totalUnknown === 0,
        "There should not be unknown verification conditions.")
      assert(report.totalInvalid > 0,
        "There should be at least one invalid verification condition.")

    }

    super.run(testName, args)
  }
}
