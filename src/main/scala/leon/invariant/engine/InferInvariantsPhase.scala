package leon
package invariant.engine

import purescala.Common._
import purescala.Definitions._
import purescala.ExprOps._
import purescala.Expressions._
import purescala.Extractors._
import purescala.Types._
import verification.VerificationReport
import invariant.templateSolvers._
import invariant.factories._
import invariant.util._
import invariant.structure.FunctionUtils._
import invariant.structure._
import transformations._
import leon.purescala.ScalaPrinter
import leon.purescala.PrettyPrinter

/**
 * @author ravi
 * This phase performs automatic invariant inference.
 */
object InferInvariantsPhase extends SimpleLeonPhase[Program, InferenceReport] {
  val name = "InferInv"
  val description = "Invariant Inference"

  val optFunctionUnroll = LeonFlagOptionDef("fullunroll", "Unroll all calls in every unroll step", false)
  val optWithMult = LeonFlagOptionDef("withmult", "Multiplication is not converted to a recursive function in VCs", false)
  val optUseReals = LeonFlagOptionDef("usereals", "Interpret the input program as a real program", false)
  val optMinBounds = LeonFlagOptionDef("minbounds", "tighten time bounds", false)
  val optInferTemp = LeonFlagOptionDef("inferTemp", "Infer templates by enumeration", false)
  val optCegis = LeonFlagOptionDef("cegis", "use cegis instead of farkas", false)
  val optStatsSuffix = LeonStringOptionDef("stats-suffix", "the suffix of the statistics file", "", "s")
  val optVCTimeout = LeonLongOptionDef("vcTimeout", "Timeout after T seconds when trying to prove a verification condition", 20, "s")
  val optDisableInfer = LeonFlagOptionDef("disableInfer", "Disable automatic inference of auxiliary invariants", false)

  override val definedOptions: Set[LeonOptionDef[Any]] =
    Set(optFunctionUnroll, optWithMult, optUseReals,
        optMinBounds, optInferTemp, optCegis, optStatsSuffix, optVCTimeout,
        optDisableInfer)

  def apply(ctx: LeonContext, program: Program): InferenceReport = {
    val inferctx = new InferenceContext(program,  ctx)
    val report = (new InferenceEngine(inferctx)).runWithTimeout()
    //println("Final Program: \n" +PrettyPrinter.apply(InferenceReportUtil.pushResultsToInput(inferctx, report.conditions)))
    report
  }
}
