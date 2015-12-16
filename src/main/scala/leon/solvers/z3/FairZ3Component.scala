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
  val optAssumePre     = LeonFlagOptionDef("assumepre",   "Assume precondition holds (pre && f(x) = body) when unfolding", false)
  val optNoChecks      = LeonFlagOptionDef("nochecks",    "Disable counter-example check in presence of foralls"   , false)
  val optUnfoldFactor  = LeonLongOptionDef("unfoldFactor", "Number of unfoldings to perform in each unfold step", default = 1, "<PosInt>")

  override val definedOptions: Set[LeonOptionDef[Any]] =
    Set(optEvalGround, optCheckModels, optFeelingLucky, optUseCodeGen, optUnrollCores, optAssumePre, optUnfoldFactor)
}

object FairZ3Component extends FairZ3Component
