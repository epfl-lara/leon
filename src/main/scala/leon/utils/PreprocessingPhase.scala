/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

import purescala.Definitions.Program

import purescala.{MethodLifting, CompleteAbstractDefinitions,CheckADTFieldsTypes}
import synthesis.{ConvertWithOracle, ConvertHoles}
import verification.InjectAsserts

object PreprocessingPhase extends TransformationPhase {

  val name = "preprocessing"
  val description = "Various preprocessings on Leon programs"

  def apply(ctx: LeonContext, p: Program): Program = {

    val phases =
      MethodLifting                 andThen
      TypingPhase                   andThen
      ConvertWithOracle             andThen
      ConvertHoles                  andThen
      CompleteAbstractDefinitions   andThen
      CheckADTFieldsTypes           andThen
      InjectAsserts


    phases.run(ctx)(p)
  }
}
