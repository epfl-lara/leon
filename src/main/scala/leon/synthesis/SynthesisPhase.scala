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
  val description = "Partial synthesis of \"choose\" constructs"

  val optManual      = LeonStringOptionDef("manual", "Manual search", default = "", "cmd")
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
    SynthesisSettings(
      manualSearch = ms,
      functions = ctx.findOption(SharedOptions.optFunctions) map { _.toSet },
      timeoutMs = ctx.findOption(SharedOptions.optTimeout) map { _ * 1000 },
      generateDerivationTrees = ctx.findOptionOrDefault(optDerivTrees),
      cegisUseOptTimeout = ctx.findOption(optCEGISOptTimeout),
      cegisUseShrink = ctx.findOption(optCEGISShrink),
      cegisUseVanuatoo = ctx.findOption(optCEGISVanuatoo),
      rules = Rules.all ++ (ms map { _ => rules.AsChoose}),
      costModel = {
        ctx.findOption(optCostModel) match {
          case None => CostModels.default
          case Some(name) => CostModels.all.find(_.name.toLowerCase == name.toLowerCase) match {
            case Some(model) => model
            case None =>
              var errorMsg = "Unknown cost model: " + name + "\n" +
                "Defined cost models: \n"

              for (cm <- CostModels.all.toSeq.sortBy(_.name)) {
                errorMsg += " - " + cm.name + (if (cm == CostModels.default) " (default)" else "") + "\n"
              }

              ctx.reporter.fatalError(errorMsg)
          }

        }
      }
    )
  }

  def run(ctx: LeonContext)(p: Program): Program = {
    val options = processOptions(ctx)

    def excludeByDefault(fd: FunDef): Boolean = fd.annotations contains "library"

    val fdFilter = {
      import OptionsHelpers._
      val ciTofd = { (ci: ChooseInfo) => ci.fd }

      filterInclusive(options.functions.map(fdMatcher), Some(excludeByDefault _)) compose ciTofd
    }

    val chooses = ChooseInfo.extractFromProgram(p).filter(fdFilter)

    var functions = Set[FunDef]()

    chooses.foreach { ci =>
      val synthesizer = new Synthesizer(ctx, p, ci, options)
      val (search, solutions) = synthesizer.validate(synthesizer.synthesize())

      val fd = ci.fd

      if (options.generateDerivationTrees) {
        val dot = new DotGenerator(search.g)
        dot.writeFile("derivation"+DotGenerator.nextId()+".dot")
      }

      val (sol, _) = solutions.head

      val expr = sol.toSimplifiedExpr(ctx, p)
      fd.body = fd.body.map(b => replace(Map(ci.source -> expr), b))
      functions += fd
    }

    for (fd <- functions) {
      ctx.reporter.info(ASCIIHelpers.title(fd.id.name))
      ctx.reporter.info(ScalaPrinter(fd))
      ctx.reporter.info("")
    }

    p
  }


}
