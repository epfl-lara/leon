/* Copyright 2009-2016 EPFL, Lausanne */

package leon.regression.repair

import leon.test._
import leon.utils._
import leon.frontends.scalac.ExtractionPhase
import leon.repair._

class RepairSuite extends LeonRegressionSuite {
  val pipeline = ExtractionPhase andThen 
    new PreprocessingPhase andThen
    RepairPhase
    
  val fileToFun = Map(
    "Compiler1.scala"   -> "desugar",
    "Heap3.scala"       -> "merge",
    "Heap4.scala"       -> "merge",
    "ListEasy.scala"    -> "pad",
    "List1.scala"       -> "pad",
    "Numerical1.scala"  -> "power",
    "MergeSort2.scala"  -> "merge"
  )
  
  for (file <- filesInResourceDir("regression/repair/", _.endsWith(".scala"))) {

    val path = file.getAbsoluteFile.toString
    val name = file.getName

    test(name) {
      if (!(fileToFun contains file.getName)) {
        fail(s"Don't know which function to repair for ${file.getName}")
      }

      val ctx = createLeonContext("--parallel", "--timeout=180", "--solvers=smt-z3", s"--functions=${fileToFun(name)}")

      pipeline.run(ctx, List(path))
      if(ctx.reporter.errorCount > 0) {
        fail("Errors during repair:\n"+ctx.reporter.asInstanceOf[TestSilentReporter].lastErrors.mkString("\n"))
      }
    }
  }
}
