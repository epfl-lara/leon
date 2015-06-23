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
import invariant.structure._
import transformations._
import leon.purescala.ScalaPrinter

/**
 * @author ravi
 * This phase performs automatic invariant inference.
 * TODO: Fix the handling of getting a template for a function, the current code is very obscure
 * TODO: should time be implicitly made positive
 */
object InferInvariantsPhase extends LeonPhase[Program, InferenceReport] {
  val name = "InferInv"
  val description = "Invariant Inference"

  val optWholeProgram = LeonFlagOptionDef("wholeprogram", "Perform an non-modular whole program analysis", false)
  val optFunctionUnroll = LeonFlagOptionDef("fullunroll", "Unroll all calls in every unroll step", false)
  val optWithMult = LeonFlagOptionDef("withmult", "Multiplication is not converted to a recursive function in VCs", false)
  val optUseReals = LeonFlagOptionDef("usereals", "Interpret the input program as a real program", false)
  val optMinBounds = LeonFlagOptionDef("minbounds", "tighten time bounds", false)
  val optInferTemp = LeonFlagOptionDef("inferTemp", "Infer templates by enumeration", false)
  val optCegis = LeonFlagOptionDef("cegis", "use cegis instead of farkas", false)
  val optStatsSuffix = LeonStringOptionDef("stats-suffix", "the suffix of the statistics file", "", "s")
  val optTimeout = LeonLongOptionDef("timeout", "Timeout after T seconds when trying to prove a verification condition.", 20, "s")

  override val definedOptions: Set[LeonOptionDef[Any]] =
    Set(optWholeProgram, optFunctionUnroll, optWithMult, optUseReals, optMinBounds, optInferTemp, optCegis, optStatsSuffix, optTimeout)

  //TODO provide options for analyzing only selected functions
  def run(ctx: LeonContext)(prog: Program): InferenceReport = {

    //control printing of statistics
    val dumpStats = true
    var timeout: Int = 20 //default timeout is 10s

    //defualt true flags
    var modularlyAnalyze = true
    var targettedUnroll = true

    //default false flags
    var tightBounds = false
    var withmult = false
    var inferTemp = false
    var enumerationRelation: (Expr, Expr) => Expr = LessEquals
    var useCegis = false
    //var maxCegisBound = 200 //maximum bound for the constants in cegis
    var maxCegisBound = 1000000000
    var statsSuff = "-stats" + FileCountGUID.getID
    var usereals = false

    for (opt <- ctx.options) (opt.optionDef.name, opt.value) match {
      case ("wholeprogram", true) => {
        //do not do a modular analysis
        modularlyAnalyze = false
      }

      case ("fullunroll", true) => {
        //do not do a modular analysis
        targettedUnroll = false
      }

      case ("minbounds", true) => {
        tightBounds = true
      }

      case ("withmult", true) => {
        withmult = true
      }

      case ("usereals", true) => {
        usereals = true
      }

      case ("inferTemp", true) => {
        inferTemp = true
        var foundStrongest = false
        //go over all post-conditions and pick the strongest relation
        prog.definedFunctions.foreach((fd) => {
          if (!foundStrongest && fd.hasPostcondition) {
            val cond = fd.postcondition.get
            simplePostTransform((e) => e match {
              case Equals(_, _) => {
                enumerationRelation = Equals.apply _
                foundStrongest = true
                e
              }
              case _ => e
            })(cond)
          }
        })
      }

      case ("cegis", true) => {
        useCegis = true
      }

      case ("timeout", timeOut: Int) =>
        timeout = timeOut

      case ("stats-suffix", suffix: String) => {
        statsSuff = suffix
      }

      case _ =>
    }

    //println("Before Inference: \n" + ScalaPrinter.apply(prog))

    /**
     * Note: when withmult is specified we convert the program to a real program
     */
    val newprog = if (usereals) {
      (new IntToRealProgram())(prog)
    } else prog

    val nlelim = new NonlinearityEliminator(withmult, if (usereals) RationalType else IntegerType)
    val finalprog = nlelim(newprog)

    //populate the inference context and invoke inferenceEngine
    val inferctx = new InferenceContext(finalprog, ctx,
      //multiplication operation
      (e1, e2) => FunctionInvocation(TypedFunDef(nlelim.multFun, nlelim.multFun.tparams.map(_.tp)), Seq(e1, e2)),
      enumerationRelation = LessEquals, modularlyAnalyze, targettedUnroll,
      dumpStats, tightBounds, withmult, usereals, inferTemp, useCegis, timeout, maxCegisBound, statsSuff)
    (new InferenceEngine(inferctx)).run()
  }
}