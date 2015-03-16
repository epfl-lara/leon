/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package frontends.scalac

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import purescala.Definitions.Program
import purescala.Definitions.{ModuleDef => LeonModuleDef, _}
import utils.{Position => LeonPosition, RangePosition => LeonRangePosition, OffsetPosition => LeonOffsetPosition}

trait SaveImports extends SubComponent {
  import global._

  val phaseName = "imports"

  val ctx: LeonContext

  var imports : Map[RefTree,List[Import]] = Map()
  
  
  // FIXME : Copy pasting code is bad.
  def scalaPosToLeonPos(p: global.Position): LeonPosition = {
    if (p == NoPosition) {
      leon.utils.NoPosition
    } else if (p.isRange) {
      val start = p.focusStart
      val end   = p.focusEnd
      LeonRangePosition(start.line, start.column, start.point,
                        end.line, end.column, end.point,
                        p.source.file.file)
    } else {
      LeonOffsetPosition(p.line, p.column, p.point,
                         p.source.file.file)
    }
  }

  
  def newPhase(prev: scala.tools.nsc.Phase): StdPhase = new Phase(prev)

  class Phase(prev: scala.tools.nsc.Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      unit.body match {
        case pkg @ PackageDef(pid,lst) =>
          
          imports += pid -> (lst collect { 
            case i : Import => i 
          })
          
          for (tree <- lst if !tree.isInstanceOf[Import] ) {
            tree.foreach {
              case imp : Import => 
                ctx.reporter.warning(
                  scalaPosToLeonPos(imp.pos),
                  "Imports will not be preserved in the AST unless they are at top-level"
                )
              case _ => 
            }
          }
          
      }
    }
  }
}
