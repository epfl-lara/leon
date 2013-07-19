/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import purescala.TreeOps._
import solvers.TrivialSolver
import solvers.z3.{FairZ3Solver,UninterpretedZ3Solver}

import purescala.Trees._
import purescala.ScalaPrinter
import purescala.Definitions.{Program, FunDef}

object SynthesisPhase extends LeonPhase[Program, Program] {
  val name        = "Synthesis"
  val description = "Synthesis"

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonFlagOptionDef(    "inplace",         "--inplace",         "Debug level"),
    LeonOptValueOptionDef("parallel",        "--parallel[=N]",    "Parallel synthesis search using N workers"),
    LeonFlagOptionDef(    "manual",          "--manual",          "Manual search"),
    LeonFlagOptionDef(    "derivtrees",      "--derivtrees",      "Generate derivation trees"),
    LeonFlagOptionDef(    "firstonly",       "--firstonly",       "Stop as soon as one synthesis solution is found"),
    LeonValueOptionDef(   "timeout",         "--timeout=T",       "Timeout after T seconds when searching for synthesis solutions .."),
    LeonValueOptionDef(   "costmodel",       "--costmodel=cm",    "Use a specific cost model for this search"),
    LeonValueOptionDef(   "functions",       "--functions=f1:f2", "Limit synthesis of choose found within f1,f2,.."),
    LeonFlagOptionDef(    "cegis:gencalls",  "--cegis:gencalls",  "Include function calls in CEGIS generators"),
    LeonFlagOptionDef(    "cegis:vanuatoo",  "--cegis:vanuatoo",  "Generate inputs using new korat-style generator")
  )

  def processOptions(ctx: LeonContext): SynthesisOptions = {
    var options = SynthesisOptions()

    for(opt <- ctx.options) opt match {
      case LeonFlagOption("manual") =>
        options = options.copy(manualSearch = true)

      case LeonFlagOption("inplace") =>
        options = options.copy(inPlace = true)

      case LeonValueOption("functions", ListValue(fs)) =>
        options = options.copy(filterFuns = Some(fs.toSet))

      case LeonValueOption("costmodel", cm) =>
        CostModel.all.find(_.name.toLowerCase == cm.toLowerCase) match {
          case Some(model) =>
            options = options.copy(costModel = model)
          case None =>

            var errorMsg = "Unknown cost model: " + cm + "\n" +
                           "Defined cost models: \n"

            for (cm <- CostModel.all.toSeq.sortBy(_.name)) {
              errorMsg += " - " + cm.name + (if(cm == CostModel.default) " (default)" else "") + "\n"
            }

            ctx.reporter.fatalError(errorMsg)
        }

      case v @ LeonValueOption("timeout", _) =>
        v.asInt(ctx).foreach { t =>
          options = options.copy(timeoutMs  = Some(t.toLong))
        } 

      case LeonFlagOption("firstonly") =>
        options = options.copy(firstOnly = true)

      case LeonFlagOption("parallel") =>
        options = options.copy(searchWorkers = 5)

      case o @ LeonValueOption("parallel", nWorkers) =>
        o.asInt(ctx).foreach { nWorkers =>
          options = options.copy(searchWorkers = nWorkers)
        }

      case LeonFlagOption("cegis:gencalls") =>
        options = options.copy(cegisGenerateFunCalls = true)

      case LeonFlagOption("cegis:vanuatoo") =>
        options = options.copy(cegisUseVanuatoo = true)

      case LeonFlagOption("derivtrees") =>
        options = options.copy(generateDerivationTrees = true)

      case _ =>
    }

    if (options.manualSearch) {
      options = options.copy(rules = rules.AsChoose +: options.rules)
    }

    options
  }

  def run(ctx: LeonContext)(p: Program): Program = {
    val options = processOptions(ctx)

    def toProcess(ci: ChooseInfo) = {
      options.filterFuns.isEmpty || options.filterFuns.get.contains(ci.fd.id.toString)
    }

    var chooses = ChooseInfo.extractFromProgram(ctx, p, options).filter(toProcess)

    val results = chooses.map { ci =>
      val (sol, isComplete) = ci.synthesizer.synthesize()

      ci -> sol.toSimplifiedExpr(ctx, p)
    }.toMap

    if (options.inPlace) {
      for (file <- ctx.files) {
        new FileInterface(ctx.reporter).updateFile(file, results)
      }
    } else {
      for ((ci, ex) <- results) {
        val middle = " In "+ci.fd.id.toString+", synthesis of: "

        val remSize = (80-middle.length)

        ctx.reporter.info("-"*math.floor(remSize/2).toInt+middle+"-"*math.ceil(remSize/2).toInt)
        ctx.reporter.info(ci.ch)
        ctx.reporter.info("-"*35+" Result: "+"-"*36)
        ctx.reporter.info(ScalaPrinter(ex))
        ctx.reporter.info("")
      }
    }

    p
  }


}
