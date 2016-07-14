/* Copyright 2009-2016 EPFL, Lausanne */

package leon.regression.verification

import leon._
import leon.test._

import leon.utils.UniqueCounter
import leon.verification.{VerificationPhase, VerificationReport}
import leon.purescala.Definitions.Program
import leon.frontends.scalac.ExtractionPhase
import leon.utils.PreprocessingPhase
import leon.solvers.isabelle.AdaptationPhase
import leon.xlang.FixReportLabels

import org.scalatest.{Reporter => _, _}

// If you add another regression test, make sure it contains exactly one object, whose name matches the file name.
// This is because we compile all tests from each folder together.
trait VerificationSuite extends LeonRegressionSuite {

  val optionVariants: List[List[String]]
  val testDir: String

  val ignored: Seq[String] = Seq()
  val desugarXLang: Boolean = false
  val isabelle: Boolean = false

  private val counter = new UniqueCounter[Unit]
  counter.nextGlobal // Start with 1

  private case class Output(report: VerificationReport, reporter: Reporter)

  private def mkTest(files: List[String], cat: String)(block: Output => Unit) = {
    val extraction =
      ExtractionPhase andThen
      new PreprocessingPhase

    val analysis =
      AdaptationPhase.when(isabelle) andThen
      VerificationPhase andThen
      FixReportLabels.when(desugarXLang)

    val ctx = createLeonContext(files:_*).copy(reporter = new TestErrorReporter)

    try {
      val (_, ast) = extraction.run(ctx, files)
      val programs = {
        val (user, lib) = ast.units partition { _.isMainUnit }
        user map ( u => Program(u :: lib) )
      }
      for ( p <- programs; options <- optionVariants) {

        val displayName = s"$cat/${p.units.head.id.name}.scala"

        val index = counter.nextGlobal
        val ts = if (ignored exists (_.endsWith(displayName)))
          ignore _
        else
          test _

        ts(f"$index%3d: $displayName ${options.mkString(" ")}", Seq()) {
          val ctx = createLeonContext(options: _*)
          try {
            val (ctx2, report) = analysis.run(ctx, p)
            block(Output(report, ctx2.reporter))
          } catch {
            case fe: LeonFatalError =>
              fail(ctx, "Verification failed", fe)
          }
        }
      }
    } catch {
      case fe: LeonFatalError =>
        test("Compilation") {
          fail(ctx, "Unexpected fatal error while setting up tests", fe)
        }
    }
  }

  private[verification] def forEachFileIn(cat: String)(block: Output => Unit) {
    val fs = filesInResourceDir(testDir + cat, _.endsWith(".scala")).toList

    fs foreach { file =>
      assert(file.exists && file.isFile && file.canRead,
        s"Benchmark ${file.getName} is not a readable file")
    }

    val files = fs map { _.getPath }

    mkTest(files, cat)(block)
  }

  protected def testValid() = forEachFileIn("valid") { output =>
    val Output(report, reporter) = output
    for ((vc, vr) <- report.vrs if vr.isInvalid) {
      fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
    }
    for ((vc, vr) <- report.vrs if vr.isInconclusive) {
      fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  protected def testInvalid() = forEachFileIn("invalid") { output =>
    val Output(report, _) = output
    assert(report.totalUnknown === 0,
      "There should not be unknown verification conditions.")
    assert(report.totalInvalid > 0,
      "There should be at least one invalid verification condition.")
  }

  protected def testUnknown() = forEachFileIn("unknown") { output =>
    val Output(report, reporter) = output
    for ((vc, vr) <- report.vrs if vr.isInvalid) {
      fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
    }
    assert(report.totalUnknown > 0,
      "There should be at least one unknown verification condition.")

    reporter.terminateIfError()
  }

  protected def testAll() = {
    testValid()
    testInvalid()
    testUnknown()
  }

  override def run(testName: Option[String], args: Args): Status = {
    testAll()
    super.run(testName, args)
  }
}
