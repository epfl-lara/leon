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
    
  val settings = Settings(verify = false, repair = true)
  val reporter = new DefaultReporter(settings)
  val ctx0 = LeonContext(
    reporter,
    new InterruptManager(reporter)
  )
  
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
    val option = LeonValueOption("functions", fileToFun(name))
    val ctx = ctx0.copy(options = option +: ctx0.options)
    test(name) {
      pipeline.run(ctx)(List(path))
    }
  }
    
  
}