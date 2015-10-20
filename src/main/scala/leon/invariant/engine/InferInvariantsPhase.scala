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
    //default values for flags
    val dumpStats = false
    var vcTimeout: Int = 15
    var targettedUnroll = true
    var tightBounds = false
    var withmult = false
    var inferTemp = false
    var enumerationRelation: (Expr, Expr) => Expr = LessEquals
    var useCegis = false
    //var maxCegisBound = 200 //maximum bound for the constants in cegis
    var maxCegisBound = 1000000000
    var statsSuff = "-stats" + FileCountGUID.getID
    var usereals = false
    var autoInference = true

    for (opt <- ctx.options) (opt.optionDef.name, opt.value) match {
      case ("fullunroll", true) =>
        targettedUnroll = false
      case ("minbounds", true) =>
        tightBounds = true
      case ("withmult", true) =>
        withmult = true
      case ("usereals", true) =>
        usereals = true
      case ("disableInfer", true) =>
        autoInference = false
      case ("inferTemp", true) =>
        inferTemp = true
      case ("cegis", true) =>
        useCegis = true
      case ("vcTimeout", timeOut: Int) =>
        vcTimeout = timeOut
      case ("stats-suffix", suffix: String) =>
        statsSuff = suffix
      case _ =>
    }
    //populate the inference context and invoke inferenceEngine
    val inferctx = new InferenceContext(program,  ctx,
        targettedUnroll, autoInference, dumpStats, tightBounds,
        withmult, usereals, inferTemp, useCegis, vcTimeout,
        maxCegisBound, statsSuff)
    val report = (new InferenceEngine(inferctx)).run()
    //println("Final Program: \n" +PrettyPrinter.apply(report.finalProgramWoInstrumentation))
    report
  }
}
