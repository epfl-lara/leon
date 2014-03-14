/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package frontends.scalac

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import purescala.Definitions.Program
import purescala.Definitions.{ModuleDef => LeonModuleDef, _}

trait LeonExtraction extends SubComponent with CodeExtraction {
  import global._

  val phaseName = "leon"

  var units: List[CompilationUnit] = Nil

  val ctx: LeonContext


  def modules = {
    new Extraction(units).extractModules
  }

  def newPhase(prev: scala.tools.nsc.Phase): StdPhase = new Phase(prev)

  class Phase(prev: scala.tools.nsc.Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      units ::= unit
    }
  }
}
