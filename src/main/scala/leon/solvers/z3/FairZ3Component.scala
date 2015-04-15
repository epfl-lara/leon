/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.z3

trait FairZ3Component extends LeonComponent {
  val name = "Z3-f"
  val description = "Fair Z3 Solver"

  val EvalGround    = LeonFlagOptionDef("evalground",  "Use evaluator on functions applied to ground arguments",  false)
  val CheckModels   = LeonFlagOptionDef("checkmodels", "Double-check counter-examples with evaluator",            false)
  val FeelingLucky  = LeonFlagOptionDef("feelinglucky","Use evaluator to find counter-examples early",            false)
  val UseCodeGen    = LeonFlagOptionDef("codegen",     "Use compiled evaluator instead of interpreter",           false)
  val UnrollCores   = LeonFlagOptionDef("unrollcores", "Use unsat-cores to drive unrolling while remaining fair", false)

  override val definedOptions: Set[LeonOptionDef[Any]] =
    Set(EvalGround, CheckModels, FeelingLucky, UseCodeGen, UnrollCores)
}

object FairZ3Component extends FairZ3Component
