/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.z3

trait FairZ3Component extends LeonComponent {
  val name = "Z3-f"
  val description = "Fair Z3 Solver"

  val optEvalGround    = LeonFlagOptionDef("evalground",  "Use evaluator on functions applied to ground arguments",  false)
  val optCheckModels   = LeonFlagOptionDef("checkmodels", "Double-check counter-examples with evaluator",            false)
  val optFeelingLucky  = LeonFlagOptionDef("feelinglucky","Use evaluator to find counter-examples early",            false)
  val optUseCodeGen    = LeonFlagOptionDef("codegen",     "Use compiled evaluator instead of interpreter",           false)
  val optUnrollCores   = LeonFlagOptionDef("unrollcores", "Use unsat-cores to drive unrolling while remaining fair", false)

  override val definedOptions: Set[LeonOptionDef[Any]] =
    Set(optEvalGround, optCheckModels, optFeelingLucky, optUseCodeGen, optUnrollCores)
}

object FairZ3Component extends FairZ3Component
