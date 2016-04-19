/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.ExprOps.replace
import purescala.ScalaPrinter
import purescala.Definitions.{Program, FunDef}

import leon.utils._
import graph._

object SynthesisPhase extends UnitPhase[Program] {
  val name        = "Synthesis"
  val description = "Partial synthesis of \"choose\" constructs. Also used by repair during the synthesis stage."

  val optManual       = LeonStringOptionDef("manual", "Manual search", default = "", "[cmd]")
  val optCostModel    = LeonStringOptionDef("costmodel", "Use a specific cost model for this search", "FIXME", "cm")
  val optDerivTrees   = LeonFlagOptionDef("derivtrees", "Generate derivation trees", false)
  val optAllowPartial = LeonFlagOptionDef("partial", "Allow partial solutions", true)

  // CEGIS options
  val optCEGISOptTimeout   = LeonFlagOptionDef("cegis:opttimeout", "Consider a time-out of CE-search as untrusted solution", true )
  val optCEGISVanuatoo     = LeonFlagOptionDef("cegis:vanuatoo",   "Generate inputs using new korat-style generator",        false)
  val optCEGISNaiveGrammar = LeonFlagOptionDef("cegis:naive",      "Use the old naive grammar for CEGIS",                    false)
  val optCEGISMaxSize      = LeonLongOptionDef("cegis:maxsize",    "Maximum size of expressions synthesized by CEGIS", 7L, "N")

  // Other rule options
  val optSpecifyRecCalls = LeonFlagOptionDef("reccalls", "Use full value as spec for introduced recursive calls", true)

  override val definedOptions : Set[LeonOptionDef[Any]] = Set(
    optManual, optCostModel, optDerivTrees, optCEGISOptTimeout, optCEGISVanuatoo,
    optCEGISNaiveGrammar, optCEGISMaxSize, optSpecifyRecCalls, optAllowPartial
  )

  def processOptions(ctx: LeonContext): SynthesisSettings = {
    val ms = ctx.findOption(optManual)
    val timeout = ctx.findOption(GlobalOptions.optTimeout)
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
      rules = Rules.all(ctx.findOptionOrDefault(optCEGISNaiveGrammar)),
      manualSearch = ms,
      functions = ctx.findOption(GlobalOptions.optFunctions) map { _.toSet },
      cegisUseOptTimeout = ctx.findOptionOrDefault(optCEGISOptTimeout),
      cegisUseVanuatoo = ctx.findOptionOrDefault(optCEGISVanuatoo),
      cegisMaxSize = ctx.findOptionOrDefault(optCEGISMaxSize).toInt
    )
  }

  def apply(ctx: LeonContext, program: Program): Unit = {
    val options = processOptions(ctx)

    val chooses = SourceInfo.extractFromProgram(ctx, program)

    var functions = Set[FunDef]()

    chooses.toSeq.sortBy(_.fd.id).foreach { ci =>
      val fd = ci.fd

      val synthesizer = new Synthesizer(ctx, program, ci, options)

      val to = new TimeoutFor(ctx.interruptManager)

      to.interruptAfter(options.timeoutMs) {
        val allowPartial = ctx.findOptionOrDefault(optAllowPartial)

        val (search, solutions) = synthesizer.validate(synthesizer.synthesize(), allowPartial)

        try {
          if (options.generateDerivationTrees) {
            val dot = new DotGenerator(search)
            dot.writeFile("derivation"+dotGenIds.nextGlobal+".dot")
          }

          solutions.headOption foreach { case (sol, _) =>
            val expr = sol.toSimplifiedExpr(ctx, program, ci.fd)
            fd.body = fd.body.map(b => replace(Map(ci.source -> expr), b))
            functions += fd
          }

        } finally {
          synthesizer.shutdown()
        }
      }
    }

    for (fd <- functions) {
      ctx.reporter.info(ASCIIHelpers.title(fd.id.name))
      ctx.reporter.info(ScalaPrinter(fd, opgm = Some(program)))
      ctx.reporter.info("")
    }

  }

}
