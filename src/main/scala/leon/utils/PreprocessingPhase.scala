/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

import purescala.Definitions.Program
import purescala.ScalaPrinter

import purescala.{MethodLifting, CompleteAbstractDefinitions}
import synthesis.{ConvertWithOracle, ConvertHoles}
import verification.InjectAsserts

object PreprocessingPhase extends TransformationPhase {

  val name = "preprocessing"
  val description = "Various preprocessings on Leon programs"

  def apply(ctx: LeonContext, p: Program): Program = {

    val phases =
      ScopingPhase                  andThen
      MethodLifting                 andThen
      TypingPhase                   andThen
      ConvertWithOracle             andThen
      ConvertHoles                  andThen
      CompleteAbstractDefinitions   andThen
      InjectAsserts


    phases.run(ctx)(p)
  }
}
