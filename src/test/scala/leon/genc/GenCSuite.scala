/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import leon.test.LeonRegressionSuite

import leon.frontends.scalac.ExtractionPhase
import leon.regression.verification.XLangVerificationSuite
import leon.purescala.Definitions.Program
import leon.utils.{ PreprocessingPhase, UniqueCounter }

import scala.concurrent._
import ExecutionContext.Implicits.global
import scala.sys.process._

import org.scalatest.{ Args, Status }

import java.io.ByteArrayInputStream
import java.nio.file.{ Files, Path }

class GenCSuite extends LeonRegressionSuite {

  private val testDir = "regression/genc/"
  private lazy val tmpDir = Files.createTempDirectory("genc")
  private val ccflags = "-std=c99 -g -O0"
  private val maxExecutionTime = 2 // seconds

  private val counter = new UniqueCounter[Unit]
  counter.nextGlobal // Start with 1

  private case class ExtendedContext(leon: LeonContext, tmpDir: Path, progName: String)

  // Tests are run as follows:
  // - before mkTest is run, all valid test are verified using XLangVerificationSuite
  // - The classic ExtractionPhase & PreprocessingPhase are run on all input files
  //   (this way the libraries are evaluated only once)
  // - A Program is constructed for each input file
  // - At this point no error should have occurred or something would be wrong
  //   with the extraction phases
  // - For each Program P:
  //   + if P is expected to be convertible to C, then we make sure that:
  //     * the GenerateCPhase run without trouble,
  //     * the generated C code compiles using a C99 compiler without error,
  //     * and that, when run, the exit code is 0
  //   + if P is expected to be non-convertible to C, then we make sure that:
  //     * the GenerateCPhase fails
  private def mkTest(files: List[String], cat: String)(block: (ExtendedContext, Program) => Unit) = {
    val extraction =
      ExtractionPhase andThen
      new PreprocessingPhase(genc = true)

    val ctx = createLeonContext(files:_*)

    try {
      val (_, ast) = extraction.run(ctx, files)

      val programs = {
        val (user, lib) = ast.units partition { _.isMainUnit }
        user map ( u => Program(u :: lib) )
      }

      for { prog <- programs } {
        val name = prog.units.head.id.name
        val ctx  = createLeonContext(s"--o=$tmpDir/$name.c")
        val xCtx = ExtendedContext(ctx, tmpDir, name)

        val displayName = s"$cat/$name.scala"
        val index       = counter.nextGlobal

        test(f"$index%3d: $displayName") {
          block(xCtx, prog)
        }
      }
    } catch {
      case fe: LeonFatalError =>
        test("Compilation") {
          fail(ctx, "Unexpected fatal error while setting up tests", fe)
        }
    }
  }

  // Run a process with a timeout and return the status code
  private def runProcess(pb: ProcessBuilder): Int = runProcess(pb.run)
  private def runProcess(p: Process): Int = {
    val f = Future(blocking(p.exitValue()))
    try {
      Await.result(f, duration.Duration(maxExecutionTime, "sec"))
    } catch {
      case _: TimeoutException =>
        p.destroy()
        throw LeonFatalError("timeout reached")
    }
  }

  // Determine which C compiler is available
  private def detectCompiler: Option[String] = {
    val testCode = "int main() { return 0; }"
    val testBinary = s"$tmpDir/test"

    // NOTE this code might print error on stderr when a non-existing compiler
    // is used. It seems that even with a special ProcessLogger the RuntimeException
    // is printed for some reason.

    def testCompiler(cc: String): Boolean = try {
      def input = new ByteArrayInputStream(testCode.getBytes())
      val process = s"$cc $ccflags -o $testBinary -xc -" #< input #&& s"$testBinary"
      runProcess(process) == 0
    } catch {
      case _: java.lang.RuntimeException => false
    }

    val knownCompiler = "cc" :: "clang" :: "gcc" :: "mingw" :: Nil
    // Note that VS is not in the list as we cannot specify C99 dialect

    knownCompiler find testCompiler
  }

  private def convert(xCtx: ExtendedContext)(prog: Program) = {
    try {
      GenerateCPhase(xCtx.leon, prog)
    } catch {
      case fe: LeonFatalError =>
        fail(xCtx.leon, "Convertion to C unexpectedly failed", fe)
    }
  }

  private def saveToFile(xCtx: ExtendedContext)(cprog: CAST.Prog) = {
    CFileOutputPhase(xCtx.leon, cprog)
  }

  private def compile(xCtx: ExtendedContext, cc: String)(unused: Unit) = {
    val basename     = s"${xCtx.tmpDir}/${xCtx.progName}"
    val sourceFile   = s"$basename.c"
    val compiledProg = basename

    val process = Process(s"$cc $ccflags $sourceFile -o $compiledProg")
    val status = runProcess(process)

    assert(status == 0, "Compilation of converted program failed")
  }

  private def evaluate(xCtx: ExtendedContext)(unused: Unit) = {
    val compiledProg = s"${xCtx.tmpDir}/${xCtx.progName}"

    // TODO memory limit
    val process = Process(compiledProg)

    val status = runProcess(process)
    assert(status == 0, s"Evaluation of converted program failed with status [$status]")
  }

  private def forEachFileIn(cat: String)(block: (ExtendedContext, Program) => Unit) {
    val fs = filesInResourceDir(testDir + cat, _.endsWith(".scala")).toList

    fs foreach { file =>
      assert(file.exists && file.isFile && file.canRead,
        s"Benchmark ${file.getName} is not a readable file")
    }

    val files = fs map { _.getPath }

    mkTest(files, cat)(block)
  }

  protected def testDirectory(cc: String, dir: String) = forEachFileIn(dir) { (xCtx, prog) =>
    val converter = convert(xCtx) _
    val saver     = saveToFile(xCtx) _
    val compiler  = compile(xCtx, cc) _
    val evaluator = evaluate(xCtx) _

    val pipeline  = converter andThen saver andThen compiler andThen evaluator

    pipeline(prog)
  }

  protected def testValid(cc: String) = testDirectory(cc, "valid")
  protected def testUnverified(cc: String) = testDirectory(cc, "unverified");

  protected def testInvalid() = forEachFileIn("invalid") { (xCtx, prog) =>
    intercept[LeonFatalError] {
      GenerateCPhase(xCtx.leon, prog)
    }
  }

  class AltVerificationSuite(override val testDir: String) extends XLangVerificationSuite {
    override def testAll() = testValid() // Test only the valid ones

    override def suiteName = "Verification Suite For GenC"

    // Add a timeout for the verification
    override val optionVariants = List(List("--solvers=smt-z3,ground"))
  }

  // Run verification suite as a nested suite
  override def nestedSuites = {
    // Use our test dir and not the one from XLangVerificationSuite
    scala.collection.immutable.IndexedSeq(new AltVerificationSuite(testDir))
  }

  protected def testAll() = {
    // Set C compiler according to the platform we're currently running on
    detectCompiler match {
      case Some(cc) =>
        testValid(cc)
        testUnverified(cc)
      case None     =>
        test("dectecting C compiler") { fail("no C compiler found") }
    }

    testInvalid()
  }

  override def run(testName: Option[String], args: Args): Status = {
    testAll()
    super.run(testName, args)
  }
}

