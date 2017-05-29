/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import leon.test.LeonRegressionSuite

import leon.DefaultReporter
import leon.frontends.scalac.ExtractionPhase
import leon.regression.verification.XLangVerificationSuite
import leon.purescala.Definitions.Program
import leon.utils.{ InterruptManager, PreprocessingPhase, UniqueCounter }

import scala.concurrent._
import ExecutionContext.Implicits.global
import scala.sys.process._

import org.scalatest.{ Args, Status }

import scala.io.Source
import java.io.{ ByteArrayInputStream, File }
import java.nio.file.{ Files, Path, Paths }

import scala.language.postfixOps

class GenCSuite extends LeonRegressionSuite {

  private val testDir = "regression/genc/"
  private lazy val tmpDir = Files.createTempDirectory("genc")
  private val timeout = 60 // seconds, for processes execution

  private val counter = new UniqueCounter[Unit]
  counter.nextGlobal // Start with 1

  private case class ExtendedContext(
    leon: LeonContext,
    progName: String, // name of the source file, without extension
    sourceDir: String, // directory in which the source lives
    inputFileOpt: Option[String], // optional path to an file to be used as stdin at runtime
    disabledOptions: Seq[String] // List of compiler (title) and "output" that should not be used for this test
  )

  private case class Compiler(title: String, name: String, options: String*) {
    lazy val flags = options mkString " "

    override def toString = title
  }

  private class WarningOrAboveReporter extends DefaultReporter(Set()) {
    override def emit(msg: Message): Unit = msg.severity match {
      case this.WARNING | this.FATAL | this.ERROR | this.INTERNAL =>
        super.emit(msg)
      case _ =>
    }
  }

  override def createLeonContext(opts: String*): LeonContext = {
    val reporter = new WarningOrAboveReporter
    Main.processOptions(opts.toList).copy(reporter = reporter, interruptManager = new InterruptManager(reporter))
  }


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
        user map { u => Program(u :: lib) }
      }

      for { prog <- programs } {
        // Retrieve the unit name and the optional input/output files
        val name       = prog.units.head.id.name
        val fileOpt    = files find { _ endsWith s"$name.scala" }
        val filePrefix = fileOpt.get dropRight ".scala".length

        val sourceDir  = new File(fileOpt.get).getParent()

        val inputName  = filePrefix + ".input"
        val inputOpt   = if (Files.isReadable(Paths.get(inputName))) Some(inputName) else None

        val disabledOptionsName = filePrefix + ".disabled"
        val disabledOptions =
          if (Files.isReadable(Paths.get(disabledOptionsName))) Source.fromFile(disabledOptionsName).getLines.toSeq
          else Nil

        val ctx  = createLeonContext(s"--o=$tmpDir/$name.c")
        val xCtx = ExtendedContext(ctx, name, sourceDir, inputOpt, disabledOptions)

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
  private def runProcess(pb: ProcessBuilder): Int = {
    val logger = ProcessLogger(stdout => info(s"[from process] $stdout"), stderr => () /* scream silently */)
    runProcessImpl(pb.run(logger))
  }

  private def runProcessImpl(p: Process): Int = {
    val f = Future(blocking(p.exitValue()))
    try {
      Await.result(f, duration.Duration(timeout, "sec"))
    } catch {
      case _: TimeoutException =>
        p.destroy()
        throw LeonFatalError("timeout reached")
    }
  }

  // Determine which C compilers are available
  private def detectCompilers: Seq[Compiler] = {
    import org.apache.commons.lang3.SystemUtils._

    val testCode = "int main() { return 0; }"
    val testSource = Files.createTempFile(tmpDir, "test", ".c")
    val testBinary = s"$tmpDir/test"

    // Because not all compiler understand `-xc` we write the test code into a file.
    Files.write(testSource, testCode.getBytes)

    // NOTE this code might print error on stderr when a non-existing compiler
    // is used. It seems that even with a special ProcessLogger the RuntimeException
    // is printed for some reason.

    def testCompiler(cc: Compiler): Boolean = {
      info(s"Testing presence of ${cc.name}")

      val result = testCompilerImpl(cc)

      if (result)
        info(s"${cc.name} is supported with parameters ${cc.flags}")
      else
        info(s"Failed to detect ${cc.name}")

      result
    }

    def testCompilerImpl(cc: Compiler): Boolean = try {
      val process =
        (if (IS_OS_UNIX) s"which ${cc.name}" else s"where.exe ${cc.name}") #&&
        s"${cc.name} ${cc.flags} -o $testBinary $testSource" #&&
        s"$testBinary" #&&
        s"${cc.name} --version"

      runProcess(process) == 0
    } catch {
      case _: java.lang.RuntimeException => false
    }

    val std99 = "-std=c99"
    val clangSanitizerAddress = "-fsanitize=address"
    val clangSanitizerOthers = "-fsanitize=undefined,safe-stack" // address mode incompatible with those
    val gccSanitizer = "-fsanitize=address,undefined"

    // For clang on OS X we make sure to use the one from brew instead of the one from Xcode
    val brewClangBin = "/usr/local/opt/llvm/bin/clang"
    val brewClangCompiler = "-I/usr/local/opt/llvm/include"
    val brewClangLinker = "-L/usr/local/opt/llvm/lib -Wl,-rpath,/usr/local/opt/llvm/lib"
    val brewClang1 = Compiler("brew.clang.address", brewClangBin, std99, clangSanitizerAddress, brewClangCompiler, brewClangLinker)
    val brewClang2 = Compiler("brew.clang.others", brewClangBin, std99, clangSanitizerOthers, brewClangCompiler, brewClangLinker)

    // Similarly for GCC, we avoid the default one on OS X
    val brewGccBin = "gcc-6" // assuming it's still version 6
    val brewGcc = Compiler("brew.gcc-6", brewGccBin, std99, gccSanitizer)

    val clang1 = Compiler("clang.address", "clang", std99, clangSanitizerAddress)
    val clang2 = Compiler("clang.other", "clang", std99, clangSanitizerOthers)
    val gcc1 = Compiler("gcc", "gcc", std99)
    val gcc2 = Compiler("gcc", "gcc", std99, gccSanitizer)
    val mingw = Compiler("mingw", "mingw", std99)

    val compcert = Compiler("compcert", "ccomp", "-fno-unprototyped", "-fstruct-passing")

    val compilers: Seq[Compiler] =
      if (IS_OS_MAC_OSX) brewClang1 :: brewClang2 :: brewGcc :: compcert :: Nil
      else if (IS_OS_LINUX) clang1 :: clang2 :: gcc1 :: gcc2 :: compcert :: Nil
      else if (IS_OS_WINDOWS) mingw :: compcert :: Nil
      else fail(s"unknown operating system $OS_NAME")

    // Note that VS is not in the list as we cannot specify C99 dialect

    compilers filter testCompiler
  }

  private def convert(xCtx: ExtendedContext)(prog: Program): CAST.Prog = {
    try {
      info(s"(CAST)${xCtx.progName}")
      GenerateCPhase.run(xCtx.leon, prog)._2
    } catch {
      case fe: LeonFatalError =>
        fail(xCtx.leon, "Conversion to C unexpectedly failed", fe)
    }
  }

  private def saveToFile(xCtx: ExtendedContext)(cprog: CAST.Prog) = {
    CFileOutputPhase(xCtx.leon, cprog)
  }

  // Check whether a regression test is disabled for a given compiler.
  // NOTE this is useful to disable error when using VLA with compcert (which doesn't all them).
  private def enabled(xCtx: ExtendedContext, cc: Compiler): Boolean = !(xCtx.disabledOptions contains cc.title)

  // Return the list of compiled programs
  private def compile(xCtx: ExtendedContext, compilers: Seq[Compiler])(unused: Unit): Seq[String] = for { cc <- compilers if enabled(xCtx, cc) } yield {
    val basename = s"$tmpDir/${xCtx.progName}"
    val sourceFile = s"$basename.c"
    val bin = s"$basename.${cc.title}"

    info(s"Compiling program for compiler ${cc.title}")
    val cmd = s"${cc.name} ${cc.flags} $sourceFile -o $bin"

    val process = Process(cmd)
    val status = runProcess(process)

    if (status != 0)
      fail(s"Compilation of converted program failed with ${cc.title}. Command was: $cmd")

    bin
  }

  // Evaluate the C program, making sure it succeeds, and return the file containing the output
  private def evaluateC(xCtx: ExtendedContext, bin: String): File = {
    // If available, use the given input file
    val baseCommand = xCtx.inputFileOpt match {
      case Some(inputFile) => bin #< new File(inputFile)
      case None            => Process(bin)
    }

    // Redirect output to a tmp file
    val outputFile = new File(s"$bin.c_output")
    val command    = baseCommand #> outputFile

    // info(s"Using input file for ${xCtx.progName}: ${xCtx.inputFileOpt.isDefined}")
    info(s"Evaluating binary ${bin split "/" last}")

    // TODO add a memory limit

    val status = runProcess(command)

    if (status != 0)
      fail(s"Evaluation of $bin failed with status [$status]")

    outputFile
  }

  // Compile and evaluate the Scala program
  private def evaluateScala(xCtx: ExtendedContext): File = {
    // NOTE Those command are based on code found in `scripts/`
    val source       = s"${xCtx.sourceDir}/${xCtx.progName}.scala"
    val leonBasePath = new File(System.getProperty("user.dir"))
    val libraryPath  = new File(leonBasePath, "library")
    val libraries    = scanFilesIn(libraryPath, { _ endsWith ".scala" }, true)
    val outClasses   = Files.createTempDirectory(tmpDir, xCtx.progName + ".out")
    val scalac       = "fsc"
    val scala        = "scala"

    info(s"Compiling & evaluating Scala program")

    val compile = s"$scalac -deprecation ${libraries.mkString(" ")} $source -d $outClasses"

    val runBase = s"$scala -cp $outClasses ${xCtx.progName}"
    val run = xCtx.inputFileOpt match {
      case Some(inputFile) => runBase #< new File(inputFile)
      case None            => Process(runBase)
    }

    val outputFile = new File(s"$tmpDir/${xCtx.progName}.scala_output")
    val command    = compile #&& (run #> outputFile)

    val status = runProcess(command)

    if (status != 0)
      fail(s"Compilation or evaluation of the source program failed")

    outputFile
  }

  private def resetFsc() {
    info(s"Shutting down fsc")
    val status = runProcess("fsc -shutdown")
    if (status != 0) info("Failed to shut down fsc")
  }

  // Evaluate both Scala and C programs, making sure their output matches
  private def evaluate(xCtx: ExtendedContext)(binaries: Seq[String]) = {
    // Read file contents as bytes to avoid encoding issues
    val cOuts = binaries map { bin => Files.readAllBytes(evaluateC(xCtx, bin).toPath) }
    val scala = Files.readAllBytes(evaluateScala(xCtx).toPath)

    // Compare outputs, unless asked not to
    if (xCtx.disabledOptions contains "output") {
      info(s"Skipping output comparision")
    } else {
      for { (c, bin) <- cOuts zip binaries } {
        info(s"Checking the result of ${bin split '/' last}")
        assert((c zip scala) forall { case (c, s) => c == s }, s"Output mismatch for $bin")
      }
    }
  }

  private def forEachFileIn(cat: String)(block: (ExtendedContext, Program) => Unit) {
    val fs = filesInResourceDir(testDir + cat, _.endsWith(".scala")).toList

    for { file <- fs }
      assert(file.exists && file.isFile && file.canRead, s"Benchmark ${file.getName} is not a readable file")

    val files = fs map { _.getPath }

    mkTest(files, cat)(block)
  }

  protected def testDirectory(compilers: Seq[Compiler], cat: String) = forEachFileIn(cat) { (xCtx, prog) =>
    val converter = convert(xCtx) _
    val saver     = saveToFile(xCtx) _
    val compiler  = compile(xCtx, compilers) _
    val evaluator = evaluate(xCtx) _

    val pipeline  = converter andThen saver andThen compiler andThen evaluator

    pipeline(prog)
  }

  protected def testValid(compilers: Seq[Compiler]) = testDirectory(compilers, "valid")
  protected def testUnverified(compilers: Seq[Compiler]) = testDirectory(compilers, "unverified");

  protected def testInvalid() = forEachFileIn("invalid") { (xCtx, prog) =>
    intercept[LeonFatalError] {
      GenerateCPhase.run(xCtx.leon, prog)._2
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
    resetFsc()

    // Set C compiler according to the platform we're currently running on
    detectCompilers match {
      case Nil =>
        test("dectecting C compiler") { fail("no C compiler found") }

      case compilers =>
        info(s"Compiler(s) used: ${compilers mkString ", "}")
        testValid(compilers)
        testUnverified(compilers)
    }

    testInvalid()
  }

  override def run(testName: Option[String], args: Args): Status = {
    testAll()
    super.run(testName, args)
  }
}

