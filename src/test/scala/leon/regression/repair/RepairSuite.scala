/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.repair

import leon._
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
    "Heap4.scala"       -> "merge",
    "ListEasy.scala"    -> "pad",
    "List1.scala"       -> "pad",
    "Numerical1.scala"  -> "power",
    "MergeSort2.scala"  -> "merge"
  )
  
  for (file <- filesInResourceDir("regression/repair/", _.endsWith(".scala")) if fileToFun contains file.getName) {
    val path = file.getAbsoluteFile.toString
    val name = file.getName

    val reporter = new TestSilentReporter
    //val reporter = new DefaultReporter(Set(utils.DebugSectionRepair))

    val ctx = LeonContext(
      reporter = reporter,
      interruptManager = new InterruptManager(reporter),
      options = Seq(
        LeonOption(SharedOptions.optFunctions)(Seq(fileToFun(name))),
        LeonOption(SharedOptions.optTimeout)(20L)
      )
    )

    test(name) {
      pipeline.run(ctx)(List(path))
      if(reporter.errorCount > 0) {
        fail("Errors during repair:\n")//+reporter.lastErrors.mkString("\n"))
      }
    }
  }
}
