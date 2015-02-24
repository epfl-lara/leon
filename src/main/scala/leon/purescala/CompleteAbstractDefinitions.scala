/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Trees._
import Extractors._
import TreeOps._
import TypeTrees._

object CompleteAbstractDefinitions extends TransformationPhase {

  val name = "Materialize abstract functions"
  val description = "Inject fake choose-like body in abstract definitions"

  def apply(ctx: LeonContext, program: Program): Program = {
    // First we create the appropriate functions from methods:
    var mdToFds  = Map[FunDef, FunDef]()

    for (u <- program.units; m <- u.modules ) { 
      // We remove methods from class definitions and add corresponding functions
      m.defs.foreach {
        case fd: FunDef if fd.body.isEmpty =>
          val id = FreshIdentifier("res", fd.returnType)

          if (fd.hasPostcondition) {
            val (pid, post) = fd.postcondition.get
          
            fd.body = Some(Choose(List(id), replaceFromIDs(Map(pid -> Variable(id)), post)))
          } else {
            fd.body = Some(Choose(List(id), BooleanLiteral(true)))
          }

        case d =>
      }
    }

    // Translation is in-place
    program
  }

}
