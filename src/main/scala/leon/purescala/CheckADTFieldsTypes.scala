/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Definitions._
import TypeOps._

object CheckADTFieldsTypes extends UnitPhase[Program] {

  val name = "ADT Fields"
  val description = "Check that fields of ADTs are hierarchy roots"

  def apply(ctx: LeonContext, program: Program) = {
    program.definedClasses.foreach {
      case ccd: CaseClassDef =>
        for(vd <- ccd.fields) {
          val tpe = vd.getType
          if (bestRealType(tpe) != tpe) {
            ctx.reporter.warning("Definition of "+ccd.id.asString(ctx)+" has a field of a sub-type ("+vd.asString(ctx)+"): " +
              "this type is not supported as-is by solvers and will be up-cast. " +
              "This may cause issues such as crashes.")
          }
        }
      case _ =>
    }
  }

}
