/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter

object CFileOutputPhase extends UnitPhase[CAST.Prog] {

  val name = "C File Output"
  val description = "Output converted C program to the specified file (default leon.c)"

  val optOutputFile = new LeonOptionDef[String] {
    val name = "o"
    val description = "Output file"
    val default = "leon.c"
    val usageRhs = "file"
    val parser = OptionParsers.stringParser
  }

  override val definedOptions: Set[LeonOptionDef[Any]] = Set(optOutputFile)

  def apply(ctx: LeonContext, program: CAST.Prog) {
    // Get the output file name from command line options, or use default
    val outputFile = new File(ctx.findOptionOrDefault(optOutputFile))
    val parent = outputFile.getParentFile()
    try {
      if (parent != null) {
        parent.mkdirs()
      }
    } catch {
      case _ : java.io.IOException => ctx.reporter.fatalError("Could not create directory " + parent)
    }

    // Output C code to the file
    try {
      val fstream = new FileWriter(outputFile)
      val out = new BufferedWriter(fstream)

      val p = new CPrinter
      p.print(program)

      out.write(p.toString)
      out.close()

      ctx.reporter.info(s"Output written to $outputFile")
    } catch {
      case _ : java.io.IOException => ctx.reporter.fatalError("Could not write on " + outputFile)
    }
  }

}
