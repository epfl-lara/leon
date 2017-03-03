/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.ExprOps.replace
import purescala.ScalaPrinter
import purescala.Definitions.{FunDef, Program}
import leon.utils._
import graph._

object SynthesisPhase extends UnitPhase[Program] {
  val name        = "Synthesis"
  val description = "Partial synthesis of \"choose\" constructs. Also used by repair during the synthesis stage."

  // General options
  val optCostModel    = LeonStringOptionDef("costmodel", "Use a specific cost model for this search", "FIXME", "cm")
  val optDerivTrees   = LeonFlagOptionDef("derivtrees", "Generate derivation trees", false)
  val optAllowPartial = LeonFlagOptionDef("partial", "Allow partial solutions", true)
  val optUserDefined  = LeonFlagOptionDef("userdefined", "Use user-defined grammars", false)
  val optUntrusted    = LeonFlagOptionDef("untrusted", "Accept a time-out of CE-search during term exploration as untrusted solution", true )

  // Pick search rules (all modes)
  val optIntroRecCalls = LeonFlagOptionDef("introreccalls", "Use a rule to introduce rec. calls outside of term exploration", true)

  // Pick mode for synthesis
  object Modes extends Enumeration {
    type Mode = Value
    val Default, Probwise, Manual = Value

    val fromName = values.map(v => v.toString.toLowerCase -> v).toMap
  }
  val optMode = LeonEnumOptionDef[Modes.Mode](
    "mode", "Mode for synthesis (available: framework, probwise, manual)", Modes.fromName, Modes.Default, "[m]"
  )

  // Manual mode options
  val optManualScript = LeonStringOptionDef("manual:script", "Give a script to manual search", default = "", "[cmd]")

  // Default mode options
  val optProbwise = LeonFlagOptionDef("probwise", "Use new probwise enumeration instead of STE", false)

  // STE-related options
  val optSTEVanuatoo = LeonFlagOptionDef("ste:vanuatoo", "Generate inputs using new korat-style generator", false)
  val optSTEMaxSize  = LeonLongOptionDef("ste:maxsize",  "Maximum size of expressions synthesized by STE", 7L, "N")

  // Probwise-enum related options
  val optProbwiseTopdownOpt   = LeonFlagOptionDef("probwise:opt"  , "Use optimized topdown enumerator", true)
  val optProbwiseTopdownCoeff = LeonLongOptionDef("probwise:coeff", "Priority coefficient for ProbwiseTopdownEnumerator (default: 24)", 24, "[value]")

  override val definedOptions: Set[LeonOptionDef[Any]] = Set(
    optCostModel, optDerivTrees, optAllowPartial, optUserDefined, optUntrusted,
    optIntroRecCalls,
    optMode,
    optManualScript,
    optProbwise,
    optSTEVanuatoo, optSTEMaxSize,
    optProbwiseTopdownOpt, optProbwiseTopdownCoeff
  )

  def processOptions(ctx: LeonContext): SynthesisSettings = {
    val timeout = ctx.findOption(GlobalOptions.optTimeout)
    val mode = ctx.findOptionOrDefault(optMode)

    if (mode == Modes.Manual && timeout.isDefined) {
      ctx.reporter.warning("Defining timeout with manual search")
    }
    val rules = mode match {
      case Modes.Manual => Rules.manual
      case Modes.Probwise => Rules.probwiseOnly
      case Modes.Default => Rules.default(
        ctx.findOptionOrDefault(optIntroRecCalls),
        ctx.findOptionOrDefault(optProbwise)
      )
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
      rules = rules,
      manualSearch = ctx.findOption(optManualScript),
      functions = ctx.findOption(GlobalOptions.optFunctions) map { _.toSet },
      steUseOptTimeout = ctx.findOptionOrDefault(optUntrusted),
      steUseVanuatoo = ctx.findOptionOrDefault(optSTEVanuatoo),
      steMaxSize = ctx.findOptionOrDefault(optSTEMaxSize).toInt,
      steUserDefinedGrammar = ctx.findOptionOrDefault(optUserDefined)
    )
  }

  def apply(ctx: LeonContext, program: Program): Unit = ctx.timers.synthesis.timed {
    val options = processOptions(ctx)

    val chooses = ctx.timers.synthesis.discovery.timed { SourceInfo.extractFromProgram(ctx, program) }

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
            val expr = sol.toSimplifiedExpr(ctx, program, ci.problem.pc)
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

    /* println("-------")
    println("Evaluator Stats!")
    println(s"partialEvalRejectionCount: ${EnumeratorStats.partialEvalRejectionCount}")
    println(s"expandNextCallCount: ${EnumeratorStats.expandNextCallCount}")
    println(s"iteratorNextCallCount: ${EnumeratorStats.iteratorNextCallCount}")
    println(s"cegisIterCount: ${EnumeratorStats.cegisIterCount}") */
  }

}
