/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import purescala.Definitions.{ Program }
import utils.{ DebugSectionTrees }

import phases._

object GenerateCPhase extends LeonPhase[Program, CAST.Prog] {

  val name = "Generate C"
  val description = "Preprocess and convert Leon's AST to C"

  val pipeline =
    Pipeline.both(NoopPhase[Program], ExtractEntryPointPhase) andThen
    ComputeDependenciesPhase andThen
    Pipeline.both(NoopPhase[Dependencies], ComputeFunCtxPhase) andThen
    Scala2IRPhase andThen
    NormalisationPhase andThen
    LiftingPhase andThen
    ReferencingPhase andThen
    IR2CPhase

  def run(ctx: LeonContext, prog: Program) = pipeline.run(ctx, prog)

}

