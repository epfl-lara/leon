/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package xlang

import purescala.Definitions.Program
import purescala.FunctionClosure
import verification._

object XLangAnalysisPhase extends TransformationPhase {

  val name = "xlang analysis"
  val description = "apply analysis on xlang"

  object VCXLangKinds {
    // TODO: something of this sort should be included
    // case object InvariantEntry extends VCKind("invariant init",           "inv. init.")
    case object InvariantPost extends VCKind("invariant postcondition", "inv. post.")
    case object InvariantInd  extends VCKind("invariant inductive",     "inv. ind.")
  }

  def apply(ctx: LeonContext, pgm: Program): Program = {
    ArrayTransformation(ctx, pgm) // In-place
    EpsilonElimination(ctx, pgm)  // In-place
    (ImperativeCodeElimination andThen FunctionClosure).run(ctx)(pgm)
  }



}
