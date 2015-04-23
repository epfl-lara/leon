/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import leon._
import purescala.Definitions.Program
import java.io.File

object FileOutputPhase extends UnitPhase[Program] {
  
  val name = "File output"
  val description = "Output parsed/generated program to the specified directory (default: leon.out)"

  val optOutputDirectory = new LeonOptionDef[String] {
    val name = "o"
    val description = "Output directory"
    val default = "leon.out"
    val usageRhs = "dir"
    val parser = (x: String) => x
  }

  override val definedOptions: Set[LeonOptionDef[Any]] = Set(optOutputDirectory)

  def apply(ctx:LeonContext, p : Program) {
    // Get the output file name from command line, or use default
    val outputFolder = ctx.findOptionOrDefault(optOutputDirectory)
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
