package leon.utils

import leon._
import purescala.Definitions.Program
import java.io.File

object FileOutputPhase extends UnitPhase[Program] {
  
  val name = "File output"
  val description = "Output parsed/generated program into a file (default: memo.out.scala)"
    
  override val definedOptions : Set[LeonOptionDef] = Set( 
     LeonValueOptionDef("o", "--o=<file>",  "Output file")
  )

  def apply(ctx:LeonContext, p : Program) {
    // Get the output file name from command line, or use default
    val outputFile = ( for (LeonValueOption("o", file) <- ctx.options) yield file ).lastOption.getOrElse("memo.out.scala")
    try {
      p.writeScalaFile(outputFile)
    } catch {
      case _ : java.io.IOException => ctx.reporter.fatalError("Could not write on " + outputFile)
    }
    ctx.reporter.info("Output written on " + outputFile)
  }
  
}
