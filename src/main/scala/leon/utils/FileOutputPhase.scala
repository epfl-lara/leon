/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import leon._
import purescala.Definitions.Program
import java.io.File

object FileOutputPhase extends UnitPhase[Program] {
  
  val name = "File output"
  val description = "Output parsed/generated program into files under the specified directory (default: leon.out)"
    
  override val definedOptions : Set[LeonOptionDef] = Set( 
     LeonValueOptionDef("o", "--o=<file>",  "Output file")
  )

  def apply(ctx:LeonContext, p : Program) {
    // Get the output file name from command line, or use default
    val outputFolder = ( for (LeonValueOption("o", file) <- ctx.options) yield file ).lastOption.getOrElse("leon.out")
    try {
      new File(outputFolder).mkdir()
    } catch {
      case _ : java.io.IOException => ctx.reporter.fatalError("Could not create directory " + outputFolder)
    }

    for (u <- p.units if u.isMainUnit) {
      val outputFile = s"$outputFolder${File.separator}${u.id.toString}.scala"
      try { u.writeScalaFile(outputFile) }
      catch {
        case _ : java.io.IOException => ctx.reporter.fatalError("Could not write on " + outputFile)
      }
    }
    ctx.reporter.info("Output written on " + outputFolder)
  }
  
}
