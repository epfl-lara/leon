
package leon
package synthesis

import purescala.TreeOps._
import solvers.z3._

import purescala.Trees._
import purescala.Common._
import purescala.ScalaPrinter
import purescala.Definitions.{Program, FunDef}

object SynthesisPhase extends LeonPhase[Program, Program] {
  val name        = "Synthesis"
  val description = "Synthesis"

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonFlagOptionDef( "inplace",         "--inplace",         "Debug level"),
    LeonFlagOptionDef( "allseeing",       "--allseeing",       "Also synthesize functions using holes"),
    LeonValueOptionDef("parallel",        "--parallel[=N]",    "Parallel synthesis search using N workers", Some("5")),
    LeonFlagOptionDef( "manual",          "--manual",          "Manual search"),
    LeonFlagOptionDef( "derivtrees",      "--derivtrees",      "Generate derivation trees"),
    LeonFlagOptionDef( "firstonly",       "--firstonly",       "Stop as soon as one synthesis solution is found", true),
    LeonValueOptionDef("timeout",         "--timeout=T",       "Timeout after T seconds when searching for synthesis solutions .."),
    LeonValueOptionDef("costmodel",       "--costmodel=cm",    "Use a specific cost model for this search"),
    LeonValueOptionDef("functions",       "--functions=f1:f2", "Limit synthesis of choose found within f1,f2,.."),
    // CEGIS options
    LeonFlagOptionDef( "cegis:gencalls",   "--cegis:gencalls",      "Include function calls in CEGIS generators",      true),
    LeonFlagOptionDef( "cegis:unintprobe", "--cegis:unintprobe",    "Check for UNSAT without bloecks and with uninterpreted functions", false),
    LeonFlagOptionDef( "cegis:bssfilter",  "--cegis:bssfilter",     "Filter non-det programs when tests pruning works well", true),
    LeonFlagOptionDef( "cegis:unsatcores", "--cegis:unsatcores",    "Use UNSAT-cores in pruning", true),
    LeonFlagOptionDef( "cegis:opttimeout", "--cegis:opttimeout",    "Consider a time-out of CE-search as untrusted solution", true),
    LeonFlagOptionDef( "cegis:vanuatoo",   "--cegis:vanuatoo",      "Generate inputs using new korat-style generator", false),
    LeonFlagOptionDef( "holes:discrete",   "--holes:discrete",      "Oracles get split", false)
  )

  def processOptions(ctx: LeonContext): SynthesisOptions = {
    var options = SynthesisOptions()

    for(opt <- ctx.options) opt match {
      case LeonFlagOption("manual", v) =>
        options = options.copy(manualSearch = v)

      case LeonFlagOption("allseeing", v) =>
        options = options.copy(allSeeing = v)

      case LeonFlagOption("inplace", v) =>
        options = options.copy(inPlace = v)

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

      case LeonFlagOption("firstonly", v) =>
        options = options.copy(firstOnly = v)

      case o @ LeonValueOption("parallel", nWorkers) =>
        o.asInt(ctx).foreach { nWorkers =>
          options = options.copy(searchWorkers = nWorkers)
        }

      case LeonFlagOption("derivtrees", v) =>
        options = options.copy(generateDerivationTrees = v)

      case LeonFlagOption("cegis:unintprobe", v) =>
        options = options.copy(cegisUseUninterpretedProbe = v)

      case LeonFlagOption("cegis:unsatcores", v) =>
        options = options.copy(cegisUseUnsatCores = v)

      case LeonFlagOption("cegis:bssfilter", v) =>
        options = options.copy(cegisUseBssFiltering = v)

      case LeonFlagOption("cegis:opttimeout", v) =>
        options = options.copy(cegisUseOptTimeout = v)

      case LeonFlagOption("cegis:gencalls", v) =>
        options = options.copy(cegisGenerateFunCalls = v)

      case LeonFlagOption("cegis:vanuatoo", v) =>
        options = options.copy(cegisUseVanuatoo = v)

      case LeonFlagOption("holes:discrete", v) =>
        options = options.copy(distreteHoles = v)

      case _ =>
    }

    if (options.manualSearch) {
      options = options.copy(
        rules = rules.AsChoose +:
                options.rules
      )
    }

    options
  }

  def run(ctx: LeonContext)(p: Program): Program = {
    val options = processOptions(ctx)

    def excludeByDefault(fd: FunDef): Boolean = (fd.annotations contains "library")

    val fdFilter = {
      import OptionsHelpers._
      val ciTofd = { (ci: ChooseInfo) => ci.fd }

      filterInclusive(options.filterFuns.map(fdMatcher), Some(excludeByDefault _)) compose ciTofd
    }

    var chooses = ChooseInfo.extractFromProgram(ctx, p, options).filter(fdFilter)

    var functions = Set[FunDef]()

    val results = chooses.map { ci =>
      val (sol, isComplete) = ci.synthesizer.synthesize()

      val fd = ci.fd

      val expr = sol.toSimplifiedExpr(ctx, p)
      fd.body = fd.body.map(b => replace(Map(ci.source -> expr), b))

      functions += fd

      ci -> expr
    }.toMap

    if (options.inPlace) {
      for (file <- ctx.files) {
        new FileInterface(ctx.reporter).updateFile(file, results)
      }
    } else {
      for (fd <- functions) {
        val middle = " "+fd.id.name+" "
        val remSize = (80-middle.length)
        ctx.reporter.info("-"*math.floor(remSize/2).toInt+middle+"-"*math.ceil(remSize/2).toInt)

        ctx.reporter.info(ScalaPrinter(fd))
        ctx.reporter.info("")
      }
    }

    p
  }


}
