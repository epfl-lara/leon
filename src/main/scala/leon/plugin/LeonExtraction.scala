/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package plugin

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import purescala.Definitions.Program

trait LeonExtraction extends SubComponent with CodeExtraction {
  import global._

  val phaseName = "leon"

  var program: Option[Program] = None

  val ctx: LeonContext

  def newPhase(prev: scala.tools.nsc.Phase): StdPhase = new Phase(prev)

  class Phase(prev: scala.tools.nsc.Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      program = new Extraction(unit).extractProgram
    }
  }
}
