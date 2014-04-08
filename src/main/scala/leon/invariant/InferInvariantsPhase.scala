package leon
package invariant

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import scala.collection.mutable.{ Set => MutableSet }
import leon.LeonContext
import leon.LeonOptionDef
import leon.LeonPhase
import leon.LeonValueOption
import leon.Reporter
import leon.verification.VerificationReport
import leon.verification.VerificationCondition

/**
 * @author ravi
 * This phase performs automatic invariant inference.
 * TODO: Fix the handling of getting a template for a function, the current code is very obscure
 * TODO: should time be implicitly made positive
 */
object InferInvariantsPhase extends LeonPhase[Program, VerificationReport] {
  val name = "InferInv"
  val description = "Invariant Inference"

  override val definedOptions: Set[LeonOptionDef] = Set(
    //LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    //LeonValueOptionDef("monotones", "--monotones=f1:f2", "Monotonic functions f1,f2,..."),
    LeonFlagOptionDef("wholeprogram", "--wholeprogram", "Perform an non-modular whole program analysis"),
    LeonFlagOptionDef("fullunroll", "--fullunroll", "Unroll all calls in every unroll step"),
    LeonFlagOptionDef("withmult", "--withmult", "Multiplication is not converted to a recursive function in VCs"),
    LeonFlagOptionDef("minbounds", "--minbounds", "tighten time bounds"),
    LeonValueOptionDef("timeout", "--timeout=T", "Timeout after T seconds when trying to prove a verification condition."),
    LeonFlagOptionDef("inferTemp", "--inferTemp=True/false", "Infer templates by enumeration"),
    LeonFlagOptionDef("cegis", "--cegis=True/false", "use cegis instead of farkas"),
    LeonValueOptionDef("stats-suffix", "--stats-suffix=<suffix string>", "the suffix of the statistics file"))

  //TODO provide options for analyzing only selected functions
  def run(ctx: LeonContext)(prog: Program): VerificationReport = {

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

    //process options
    for (opt <- ctx.options) opt match {
      //      case LeonValueOption("functions", ListValue(fs)) =>
      //        functionsToAnalyse ++= fs

      case LeonFlagOption("wholeprogram", true) => {
        //do not do a modular analysis        
        modularlyAnalyze = false
      }

      case LeonFlagOption("fullunroll", true) => {
        //do not do a modular analysis
        targettedUnroll = false
      }

      case LeonFlagOption("minbounds", true) => {
        tightBounds = true
      }

      case LeonFlagOption("withmult", true) => {
        withmult = true
      }

      case v @ LeonFlagOption("inferTemp", true) => {

        inferTemp = true
        var foundStrongest = false
        //go over all post-conditions and pick the strongest relation
        prog.definedFunctions.foreach((fd) => {
          if (!foundStrongest && fd.hasPostcondition) {
            val cond = fd.postcondition.get._2
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

      case v @ LeonFlagOption("cegis", true) => {
        useCegis = true
      }

      case v @ LeonValueOption("timeout", _) =>
        timeout = v.asInt(ctx).get

      case v @ LeonValueOption("stats-suffix", ListValue(fs)) => {
        statsSuff = fs(0)
      }

      case _ =>
    }
    
    /**
     * Note: when withmult is specified we convert the program to a real program
     */
    val usereals = withmult
    val newprog = if (usereals) {
      (new IntToRealProgram())(prog)
    } else prog
    val nlelim = new NonlinearityEliminator(withmult, if(usereals) RealType else Int32Type)
    
    //populate the inference context and invoke inferenceEngine
    val inferctx = new InferenceContext(nlelim(newprog), ctx, nlelim.multFun, nlelim.pivMultFun,      
      enumerationRelation = LessEquals, modularlyAnalyze, targettedUnroll,
      dumpStats, tightBounds, withmult, usereals, inferTemp, useCegis, timeout, maxCegisBound, statsSuff)
    (new InferenceEngine(inferctx)).run()
  }
}
