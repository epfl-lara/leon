/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.verification

import leon._
import leon.test._

import leon.verification.VerificationReport
import leon.purescala.Definitions.Program
import leon.frontends.scalac.ExtractionPhase
import leon.utils.PreprocessingPhase

import _root_.smtlib.interpreters._

import java.io.File

// If you add another regression test, make sure it contains one object whose name matches the file name
// This is because we compile all tests from each folder separately.
trait VerificationRegression extends LeonTestSuite {

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

  private def mkTest(files: List[String], leonOptions : Seq[String], forError: Boolean)(block: Output=>Unit) = {
    val extraction = 
      ExtractionPhase andThen
      PreprocessingPhase andThen
      pipeFront

    if(forError) {
      intercept[LeonFatalError]{
        extraction.run(createLeonContext((files ++ leonOptions):_*))(files)
      }
    } else {
      val ctx = createLeonContext(leonOptions:_*)
      val ast = extraction.run(createLeonContext((files ++ leonOptions):_*))(files)
      val programs = {
        val (user, lib) = ast.units partition { _.isMainUnit }
        user map { u => Program(u.id.freshen, u :: lib) }
      }
      for (p <- programs; displayName = p.id.name) test("%3d: %s %s".format(nextInt(), displayName, leonOptions.mkString(" "))) {
        val report = pipeBack.run(ctx)(p)
        block(Output(report, ctx.reporter))
      }
    }
  }

  private[verification] def forEachFileIn(cat : String, forError: Boolean = false)(block : Output=>Unit) {
    val fs = filesInResourceDir( testDir + cat, _.endsWith(".scala")).toList

    fs foreach { file => 
      assert(file.exists && file.isFile && file.canRead,
        "Benchmark %s is not a readable file".format(file.getName))
    }

    val files = fs map { _.getPath }

    // If error, try to verify each file separately (and fail for each one)
    val groupedFiles = if (forError) files map (List(_)) else List(files)

    for (files <- groupedFiles; options <- optionVariants) {
      mkTest(files, options, forError)(block)
    }
  }
  
  
}
