/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.ExprOps._

import purescala.ScalaPrinter
import purescala.Definitions.{Program, FunDef}
import leon.utils.ASCIIHelpers

import graph._

object SynthesisPhase extends LeonPhase[Program, Program] {
  val name        = "Synthesis"
  val description = "Partial synthesis of \"choose\" constructs. Also used by repair during the synthesis stage."

  val optManual      = LeonStringOptionDef("manual", "Manual search", default = "", "[cmd]")
  val optCostModel   = LeonStringOptionDef("costmodel", "Use a specific cost model for this search", "FIXME", "cm")
  val optDerivTrees  = LeonFlagOptionDef( "derivtrees", "Generate derivation trees", false)

  // CEGIS options
  val optCEGISShrink     = LeonFlagOptionDef( "cegis:shrink",     "Shrink non-det programs when tests pruning works well",  true)
  val optCEGISOptTimeout = LeonFlagOptionDef( "cegis:opttimeout", "Consider a time-out of CE-search as untrusted solution", true)
  val optCEGISVanuatoo   = LeonFlagOptionDef( "cegis:vanuatoo",   "Generate inputs using new korat-style generator",       false)

  override val definedOptions : Set[LeonOptionDef[Any]] =
    Set(optManual, optCostModel, optDerivTrees, optCEGISShrink, optCEGISOptTimeout, optCEGISVanuatoo)

  def processOptions(ctx: LeonContext): SynthesisSettings = {
    val ms = ctx.findOption(optManual)
    val timeout = ctx.findOption(SharedOptions.optTimeout)
    if (ms.isDefined && timeout.isDefined) {
      ctx.reporter.warning("Defining timeout with manual search")
    }
    val costModel = {
      ctx.findOption(optCostModel) match {
        case None => CostModels.default
        case Some(name) => CostModels.all.find(_.name.toLowerCase == name.toLowerCase) getOrElse {
          var errorMsg = "Unknown cost model: " + name + "\n" +
            "Defined cost models: \n"

          for (cm <- CostModels.all.toSeq.sortBy(_.name)) {
            errorMsg += " - " + cm.name + (if (cm == CostModels.default) " (default)" else "") + "\n"
          }

          ctx.reporter.fatalError(errorMsg)
        }
      }
    }

    SynthesisSettings(
      timeoutMs = timeout map { _ * 1000 },
      generateDerivationTrees = ctx.findOptionOrDefault(optDerivTrees),
      costModel = costModel,
      rules = Rules.all ++ (if(ms.isDefined) Seq(rules.AsChoose, rules.SygusCVC4) else Seq()),
      manualSearch = ms,
      functions = ctx.findOption(SharedOptions.optFunctions) map { _.toSet },
      cegisUseOptTimeout = ctx.findOption(optCEGISOptTimeout),
      cegisUseShrink = ctx.findOption(optCEGISShrink),
      cegisUseVanuatoo = ctx.findOption(optCEGISVanuatoo)
    )
  }

  def run(ctx: LeonContext)(program: Program): Program = {
    val options = processOptions(ctx)


    val chooses = ChooseInfo.extractFromProgram(ctx, program)

    var functions = Set[FunDef]()

    chooses.toSeq.sortBy(_.fd.id).foreach { ci =>
      val fd = ci.fd

      val synthesizer = new Synthesizer(ctx, program, ci, options)

      val (search, solutions) = synthesizer.validate(synthesizer.synthesize(), true)

      try {
        if (options.generateDerivationTrees) {
          val dot = new DotGenerator(search.g)
          dot.writeFile("derivation"+dotGenIds.nextGlobal+".dot")
        }

        val (sol, _) = solutions.head

        val expr = sol.toSimplifiedExpr(ctx, program)
        fd.body = fd.body.map(b => replace(Map(ci.source -> expr), b))
        functions += fd
      } finally {
        synthesizer.shutdown()
      }
    }

    for (fd <- functions) {
      ctx.reporter.info(ASCIIHelpers.title(fd.id.name))
      ctx.reporter.info(ScalaPrinter(fd, opgm = Some(program)))
      ctx.reporter.info("")
    }

    program
  }


}
