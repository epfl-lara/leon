/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._

object CompleteAbstractDefinitions extends TransformationPhase {

  val name = "Materialize abstract functions"
  val description = "Inject fake choose-like body in abstract definitions"

  def apply(ctx: LeonContext, program: Program): Program = {
    for (u <- program.units; m <- u.modules; fd <- m.definedFunctions; if fd.body.isEmpty) {
      val post = fd.postcondition getOrElse (
        Lambda(Seq(ValDef(FreshIdentifier("res", fd.returnType))), BooleanLiteral(true))
      )
      fd.body = Some(Choose(post))
    }
    // Translation is in-place
    program
  }

}
