/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.frontends

import leon._
import java.io.File

class FrontEndsTest extends leon.test.LeonTestSuite {
  // Hard-code output directory, for Eclipse purposes
  lazy val tmpPath = java.nio.file.Files.createTempDirectory("leon-frontends");

  private def forEachFileIn(path : String)(block : File => Unit) {
    val fs = filesInResourceDir(path, _.endsWith(".scala"))

    for(f <- fs) {
      block(f)
    } 
  }
   
  val pipeline1 = 
    frontends.scalac.ExtractionPhase andThen
    utils.ScopingPhase andThen
    purescala.MethodLifting andThen
    utils.TypingPhase andThen
    purescala.CompleteAbstractDefinitions andThen
    utils.FileOutputPhase
   
  val pipeline2 = 
    frontends.scalac.ExtractionPhase andThen
    utils.ScopingPhase andThen
    purescala.MethodLifting andThen
    utils.TypingPhase andThen
    purescala.CompleteAbstractDefinitions andThen
    purescala.RestoreMethods andThen
    utils.FileOutputPhase
    
  forEachFileIn("regression/frontends" ) { f => 
      testExtr(f)
  }
   
  def testExtr(f : File) {
    val outFileName1 = tmpPath.toString ++ "/" ++ f.getName 
    val outFileName2 = tmpPath.toString ++ "/restored" ++ f.getName 
    test ("Testing " + f.getName) {
      // Compile original file
      val timeOut = 2
      val settings = testContext.settings.copy(   
        debugSections = Set()
      )
      val ctx1 = testContext.copy(
        // We want a reporter that actually prints some output
        //reporter = new DefaultReporter(settings),
        settings = settings,
        options =  testContext.options :+ LeonValueOption("o", outFileName1)
      )
      
      val ctx2 = ctx1.copy(
        //reporter = new DefaultReporter(settings),
        settings = settings,
        options = testContext.options :+ LeonValueOption("o", outFileName2 )
      )
      
      pipeline1.run(ctx1)(List(f.getAbsolutePath()))
      pipeline2.run(ctx2)(List(f.getAbsolutePath()))

    }
    
  }
}
