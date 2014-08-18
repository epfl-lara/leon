/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package utils

import purescala.Definitions.Program

import purescala.{MethodLifting, CompleteAbstractDefinitions}
import synthesis.{ConvertWithOracle, ConvertHoles}

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
      InjectAsserts

    phases.run(ctx)(p)
  }
}
