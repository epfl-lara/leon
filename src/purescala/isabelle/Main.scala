package purescala.isabelle

import purescala.Reporter
import purescala.Trees._
import purescala.Definitions._
import purescala.Extensions._
import purescala.Settings
import purescala.Common.Identifier

import java.io._

class Main(reporter : Reporter) extends Analyser(reporter) {
  val description = "Generates Isabelle source"
  override val shortDescription = "isabelle"

  def analyse(program : Program) : Unit = {
    val file = File.createTempFile("isabelle", ".thy")

    val out = new BufferedWriter(new FileWriter(file))

    out.write("text")

    out.close

    reporter.info("The file name is : " + file.getPath.toString)

    reporter.info(program)
    reporter.info("Done with Isabelle translation.")
  }

}
