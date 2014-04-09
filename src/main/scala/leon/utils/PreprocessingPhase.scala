/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package utils

import purescala.Definitions.Program

import purescala.{MethodLifting, CompleteAbstractDefinitions}

object PreprocessingPhase extends TransformationPhase {

  val name = "preprocessing"
  val description = "Various preprocessings on Leon programs"

  def apply(ctx: LeonContext, p: Program): Program = {

    val phases =
      MethodLifting                 andThen
      TypingPhase                   andThen
      CompleteAbstractDefinitions

    phases.run(ctx)(p)
  }
}
