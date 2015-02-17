package leon.test.repair

import leon.test._
import leon._
import leon.utils._
import leon.frontends.scalac.ExtractionPhase
import leon.repair._

class RepairSuite extends LeonTestSuite {
  val pipeline = ExtractionPhase andThen 
    PreprocessingPhase andThen
    RepairPhase
    
  val fileToFun = Map(
    "Compiler1.scala"   -> "desugar",
    "Heap4.scala"       -> "merge",
    "List1.scala"       -> "_pad",
    "Numerical1.scala"  -> "power",
    "MergeSort2.scala"  -> "merge"
  )
  
  for (file <- filesInResourceDir("regression/repair/")) {
    val path = file.getAbsoluteFile().toString
    val name = file.getName()

    val reporter = new TestSilentReporter

    val ctx = LeonContext(
      reporter = reporter,
      interruptManager = new InterruptManager(reporter),
      options = Seq(LeonValueOption("functions", fileToFun(name)))
    )

    test(name) {
      pipeline.run(ctx)(List(path))
      if(reporter.errorCount > 0) {
        fail("Errors during repair!")
      }
    }
  }
}
