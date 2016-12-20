/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

import purescala.Definitions.Program
import java.io.File

object RawFileOutputPhase extends UnitPhase[String] {
  
  val name = "Raw file output"
  val description = "Output any string (default: output.html)"

  val optOutputFile = LeonStringOptionDef("o", "Output file", "output.html", "file.extension")
  override val definedOptions: Set[LeonOptionDef[Any]] = Set(optOutputFile)

  def apply(ctx:LeonContext, s : String) {
    // Get the output file name from command line, or use default
    val outputFileName = ctx.findOptionOrDefault(optOutputFile)
    val outputFile = new File(outputFileName).getCanonicalFile()
    if(outputFile.getParentFile != null || !outputFile.getParentFile.exists()) {
      try {
        outputFile.getParentFile.mkdirs()
      } catch {
        case _ : java.io.IOException => ctx.reporter.fatalError("Could not create directory " + outputFileName)
      }
    }
    try {
      import java.io.FileWriter
      import java.io.BufferedWriter
      val fstream = new FileWriter(outputFile)
      val out = new BufferedWriter(fstream)
      out.write(s)
      out.close()
    }
    catch {
      case _ : java.io.IOException => ctx.reporter.fatalError("Could not write on " + outputFile)
    }
    ctx.reporter.info("Output written on " + outputFile)
  }
}
