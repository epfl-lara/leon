/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package frontends.scalac

import scala.tools.nsc._

trait AddTypeAnnotations extends SubComponent with ASTExtractors {
  import global._
  import ExtractorHelpers._

  val phaseName = "addtypeannotations"

  val ctx: LeonContext

  var imports : Map[RefTree,List[Import]] = Map()
  
  def newPhase(prev: scala.tools.nsc.Phase): StdPhase = new Phase(prev)

  class Phase(prev: scala.tools.nsc.Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      val transformer = new Transformer { 
        override def transform(tree : Tree) : Tree = tree match { 
          case d@DefDef(_,_,_,_,tpt,
            a@Apply(
              s@Select(
                bd, 
                nameEns@ExNamed("ensuring")
              ),
              f
            )
          ) => (bd,tpt.symbol) match {
            case (Typed(_,_), _) | (_, null) => d
            case _ => d.copy(rhs = 
              Apply(
                Select(
                  Typed(bd,tpt.duplicate.setPos(bd.pos.focus)).setPos(bd.pos),
                  nameEns
                ).setPos(s.pos),
                f         
              ).setPos(a.pos)
            ).setPos(d.pos)
          }
          case other => super.transform(other)
        }
      }
      unit.body = transformer.transform(unit.body)
    }
  }
}
