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

import scala.io.Source
import java.io.{ ByteArrayInputStream, File }
import java.nio.file.{ Files, Path, Paths }

class GenCSuite extends LeonRegressionSuite {

  private val testDir = "regression/genc/"
  private lazy val tmpDir = Files.createTempDirectory("genc")
  private val ccflags = "-std=c99 -g -O0"
  private val timeout = 60 // seconds, for processes execution

  private val counter = new UniqueCounter[Unit]
  counter.nextGlobal // Start with 1

  private case class ExtendedContext(
    leon: LeonContext,
    progName: String,            // name of the source file, without extention
    sourceDir: String,           // directory in which the source lives
    inputFileOpt: Option[String] // optional path to an file to be used as stdin at runtime
  )

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
  //     * and that, when run, the exit code is 0;
  //     * additionally, we compile the original scala program and evaluate it,
  //     * and, finally, we compare the output of the C and Scala program.
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
        // Retrieve the unit name and the optional input/output files
        val name       = prog.units.head.id.name
        val fileOpt    = files find { _ endsWith s"$name.scala" }
        val filePrefix = fileOpt.get dropRight ".scala".length

        val sourceDir  = new File(fileOpt.get).getParent()

        val inputName  = filePrefix + ".input"
        val inputOpt   = if (Files.isReadable(Paths.get(inputName))) Some(inputName) else None

        val ctx  = createLeonContext(s"--o=$tmpDir/$name.c")
        val xCtx = ExtendedContext(ctx, name, sourceDir, inputOpt)

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
  private def runProcess(pb: ProcessBuilder): Int =
    runProcess(pb.run)

  private def runProcess(p: Process): Int = {
    val f = Future(blocking(p.exitValue()))
    try {
      Await.result(f, duration.Duration(timeout, "sec"))
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
    val basename     = s"$tmpDir/${xCtx.progName}"
    val sourceFile   = s"$basename.c"
    val compiledProg = basename

    val process = Process(s"$cc $ccflags $sourceFile -o $compiledProg")
    val status = runProcess(process)

    assert(status == 0, "Compilation of converted program failed")
  }

  // Evaluate the C program, making sure it succeeds, and return the file containing the output
  private def evaluateC(xCtx: ExtendedContext): File = {
    val compiledProg = s"$tmpDir/${xCtx.progName}"

    // If available, use the given input file
    val baseCommand = xCtx.inputFileOpt match {
      case Some(inputFile) => compiledProg #< new File(inputFile)
      case None            => Process(compiledProg)
    }

    // Redirect output to a tmp file
    val outputFile = new File(s"$compiledProg.c_output")
    val command    = baseCommand #> outputFile

    // println(s"Using input file for ${xCtx.progName}: ${xCtx.inputFileOpt.isDefined}")

    // TODO add a memory limit

    val status = runProcess(command)
    assert(status == 0, s"Evaluation of converted program failed with status [$status]")

    outputFile
  }

  // Compile and evalue the Scala program
  private def evaluateScala(xCtx: ExtendedContext): File = {
    // NOTE Those command are based on code found in `scripts/`
    val source       = s"${xCtx.sourceDir}/${xCtx.progName}.scala"
    val leonBasePath = new File(System.getProperty("user.dir"))
    val libraryPath  = new File(leonBasePath, "library")
    val libraries    = scanFilesIn(libraryPath, { _ endsWith ".scala" }, true)
    val outClasses   = Files.createTempDirectory(tmpDir, xCtx.progName + ".out")
    val scalac       = "fsc"
    val scala        = "scala"

    val compile = s"$scalac -deprecation ${libraries.mkString(" ")} $source -d $outClasses"

    val runBase = s"$scala -cp $outClasses ${xCtx.progName}"
    val run = xCtx.inputFileOpt match {
      case Some(inputFile) => runBase #< new File(inputFile)
      case None            => Process(runBase)
    }

    // println(s"COMPILE: $compile")
    // println(s"RUN: $run")

    val outputFile = new File(s"$tmpDir/${xCtx.progName}.scala_output")
    val command    = compile #&& (run #> outputFile)

    val status = runProcess(command)
    assert(status == 0, s"Compilation or evaluation of the source program failed")

    outputFile
  }

  // Evaluate both Scala and C programs, making sure their output matches
  private def evaluate(xCtx: ExtendedContext)(unused: Unit) = {
    val c     = Source.fromFile(evaluateC(xCtx)).getLines
    val scala = Source.fromFile(evaluateScala(xCtx)).getLines

    // Compare outputs
    assert((c zip scala) forall { case (c, s) => c == s }, "Output mismatch")
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

  protected def testDirectory(cc: String, cat: String) = forEachFileIn(cat) { (xCtx, prog) =>
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

