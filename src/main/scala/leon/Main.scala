/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import leon.utils._

object Main {

  lazy val allPhases: List[LeonPhase[_, _]] = {
    List(
      frontends.scalac.ExtractionPhase,
      frontends.scalac.ClassgenPhase,
      utils.TypingPhase,
      utils.FileOutputPhase,
      purescala.RestoreMethods,
      xlang.AntiAliasingPhase,
      xlang.EpsilonElimination,
      xlang.ImperativeCodeElimination,
      xlang.FixReportLabels,
      xlang.XLangDesugaringPhase,
      purescala.FunctionClosure,
      synthesis.SynthesisPhase,
      termination.TerminationPhase,
      verification.VerificationPhase,
      repair.RepairPhase,
      evaluators.EvaluationPhase,
      solvers.isabelle.AdaptationPhase,
      solvers.isabelle.IsabellePhase,
      transformations.InstrumentationPhase,
      invariant.engine.InferInvariantsPhase,
      laziness.LazinessEliminationPhase,
      genc.GenerateCPhase,
      genc.CFileOutputPhase
    )
  }

  // Add whatever you need here.
  lazy val allComponents : Set[LeonComponent] = allPhases.toSet ++ Set(
    solvers.unrolling.UnrollingProcedure, MainComponent, GlobalOptions, solvers.smtlib.SMTLIBCVC4Component, solvers.isabelle.Component
  )

  /*
   * This object holds the options that determine the selected pipeline of Leon.
   * Please put any further such options here to have them print nicely in --help message.
   */
  object MainComponent extends LeonComponent {
    val name = "main"
    val description = "Selection of Leon functionality. Default: verify"

    val optEval        = LeonStringOptionDef("eval", "Evaluate ground functions through code generation or evaluation (default: evaluation)", "default", "[codegen|default]")
    val optTermination = LeonFlagOptionDef("termination", "Check program termination. Can be used along --verify",     false)
    val optRepair      = LeonFlagOptionDef("repair",      "Repair selected functions",                                 false)
    val optSynthesis   = LeonFlagOptionDef("synthesis",   "Partial synthesis of choose() constructs",                  false)
    val optIsabelle    = LeonFlagOptionDef("isabelle",    "Run Isabelle verification",                                 false)
    val optNoop        = LeonFlagOptionDef("noop",        "No operation performed, just output program",               false)
    val optVerify      = LeonFlagOptionDef("verify",      "Verify function contracts",                                 false)
    val optHelp        = LeonFlagOptionDef("help",        "Show help message",                                         false)
    val optInstrument  = LeonFlagOptionDef("instrument",  "Instrument the code for inferring time/depth/stack bounds", false)
    val optInferInv    = LeonFlagOptionDef("inferInv",    "Infer invariants from (instrumented) the code",             false)
    val optLazyEval    = LeonFlagOptionDef("lazy",        "Handles programs that may use the 'lazy' construct",        false)
    val optGenc        = LeonFlagOptionDef("genc",        "Generate C code",                                           false)

    override val definedOptions: Set[LeonOptionDef[Any]] =
      Set(optTermination, optRepair, optSynthesis, optIsabelle, optNoop, optHelp, optEval, optVerify, optInstrument, optInferInv, optLazyEval, optGenc)
  }

  lazy val allOptions: Set[LeonOptionDef[Any]] = allComponents.flatMap(_.definedOptions)

  def displayHelp(reporter: Reporter, error: Boolean) = {

    reporter.title(MainComponent.description)
    for (opt <- MainComponent.definedOptions.toSeq.sortBy(_.name)) {
      reporter.info(opt.helpString)
    }
    reporter.info("")

    reporter.title("Additional global options")
    for (opt <- GlobalOptions.definedOptions.toSeq.sortBy(_.name)) {
      reporter.info(opt.helpString)
    }
    reporter.info("")

    reporter.title("Additional options, by component:")

    for (c <- (allComponents - MainComponent - GlobalOptions).toSeq.sortBy(_.name) if c.definedOptions.nonEmpty) {
      reporter.info("")
      reporter.info(s"${c.name} (${c.description})")
      for (opt <- c.definedOptions.toSeq.sortBy(_.name)) {
        // there is a non-breaking space at the beginning of the string :)
        reporter.info(opt.helpString)
      }
    }
    exit(error)
  }

  def displayVersion(reporter: Reporter) = {
    reporter.title("Leon verification and synthesis tool (http://leon.epfl.ch/)")
    reporter.info("")
  }

  private def exit(error: Boolean) = sys.exit(if (error) 1 else 0)

  def processOptions(args: Seq[String]): LeonContext = {

    val initReporter = new DefaultReporter(Set())

    val options = args.filter(_.startsWith("--"))

    val files = args.filterNot(_.startsWith("-")).map(new java.io.File(_))

    val leonOptions: Seq[LeonOption[Any]] = options.map { opt =>
      val (name, value) = OptionsHelpers.nameValue(opt).getOrElse(
        initReporter.fatalError(
          s"Malformed option $opt. Options should have the form --name or --name=value"
        )
      )
      // Find respective LeonOptionDef, or report an unknown option
      val df = allOptions.find(_.name == name).getOrElse{
        initReporter.fatalError(
          s"Unknown option: $name\n" +
          "Try 'leon --help' for more information."
        )
      }
      df.parse(value)(initReporter)
    }

    val reporter = new DefaultReporter(
      leonOptions.collectFirst {
        case LeonOption(GlobalOptions.optDebug, sections) =>
          sections.asInstanceOf[Set[DebugSection]]
      }.getOrElse(Set[DebugSection]())
    )

    reporter.whenDebug(DebugSectionOptions) { debug =>
      debug("Options considered by Leon:")
      for (lo <- leonOptions) debug(lo.toString)
    }

    LeonContext(
      reporter = reporter,
      files = files,
      options = leonOptions,
      interruptManager = new InterruptManager(reporter)
    )
  }

  def computePipeline(ctx: LeonContext): Pipeline[List[String], Any] = {

    import purescala.Definitions.Program
    import purescala.RestoreMethods
    import utils.FileOutputPhase
    import frontends.scalac.{ ExtractionPhase, ClassgenPhase }
    import synthesis.SynthesisPhase
    import termination.TerminationPhase
    import xlang.FixReportLabels
    import verification.VerificationPhase
    import repair.RepairPhase
    import evaluators.EvaluationPhase
    import solvers.isabelle.IsabellePhase
    import genc.GenerateCPhase
    import genc.CFileOutputPhase
    import MainComponent._
    import invariant.engine.InferInvariantsPhase
    import transformations.InstrumentationPhase
    import laziness._

    val helpF = ctx.findOptionOrDefault(optHelp)
    val noopF = ctx.findOptionOrDefault(optNoop)
    val synthesisF = ctx.findOptionOrDefault(optSynthesis)
    val repairF = ctx.findOptionOrDefault(optRepair)
    val isabelleF = ctx.findOptionOrDefault(optIsabelle)
    val terminationF = ctx.findOptionOrDefault(optTermination)
    val verifyF = ctx.findOptionOrDefault(optVerify)
    val gencF = ctx.findOptionOrDefault(optGenc)
    val evalF = ctx.findOption(optEval).isDefined
    val inferInvF = ctx.findOptionOrDefault(optInferInv)
    val instrumentF = ctx.findOptionOrDefault(optInstrument)
    val lazyevalF = ctx.findOptionOrDefault(optLazyEval)
    val analysisF = verifyF && terminationF
    // Check consistency in options

    if (helpF) {
      displayVersion(ctx.reporter)
      displayHelp(ctx.reporter, error = false)
    } else {
      val pipeBegin: Pipeline[List[String], Program] =
        ClassgenPhase andThen
        ExtractionPhase andThen
        new PreprocessingPhase(genc = gencF)

      val verification =
        VerificationPhase andThen
        FixReportLabels andThen
        PrintReportPhase
      val termination = TerminationPhase andThen PrintReportPhase

      val pipeProcess: Pipeline[Program, Any] = {
        if (noopF) RestoreMethods andThen FileOutputPhase
        else if (synthesisF) SynthesisPhase
        else if (repairF) RepairPhase
        else if (analysisF) Pipeline.both(verification, termination)
        else if (terminationF) termination
        else if (isabelleF) IsabellePhase andThen PrintReportPhase
        else if (evalF) EvaluationPhase
        else if (inferInvF) InferInvariantsPhase
        else if (instrumentF) InstrumentationPhase andThen FileOutputPhase
        else if (gencF) GenerateCPhase andThen CFileOutputPhase
        else if (lazyevalF) LazinessEliminationPhase
        else verification
      }

      pipeBegin andThen
        pipeProcess
    }
  }

  private var hasFatal = false

  def main(args: Array[String]) {
    val argsl = args.toList

    // Process options
    val ctx = try {
      processOptions(argsl)
    } catch {
      case LeonFatalError(None) =>
        exit(error = true)

      case LeonFatalError(Some(msg)) =>
        // For the special case of fatal errors not sent though Reporter, we
        // send them through reporter one time
        try {
          new DefaultReporter(Set()).fatalError(msg)
        } catch {
          case _: LeonFatalError =>
        }

        exit(error = true)
    }

    ctx.interruptManager.registerSignalHandler()

    val doWatch = ctx.findOptionOrDefault(GlobalOptions.optWatch)

    if (doWatch) {
      val watcher = new FilesWatcher(ctx, ctx.files ++ Build.libFiles.map { new java.io.File(_) })
      watcher.onChange {
        execute(args, ctx)
      }
    } else {
      execute(args, ctx)
    }

    exit(hasFatal)
  }

  def execute(args: Seq[String], ctx0: LeonContext): Unit = {
    val ctx = ctx0.copy(reporter = new DefaultReporter(ctx0.reporter.debugSections))

    try {
      // Compute leon pipeline
      val pipeline = computePipeline(ctx)

      val timer = ctx.timers.total.start()

      // Run pipeline
      val (ctx2, _) = pipeline.run(ctx, args.toList)

      timer.stop()

      ctx2.reporter.whenDebug(DebugSectionTimers) { debug =>
        ctx2.timers.outputTable(debug)
      }
      hasFatal = false
    } catch {
      case LeonFatalError(None) =>
        hasFatal = true

      case LeonFatalError(Some(msg)) =>
        // For the special case of fatal errors not sent though Reporter, we
        // send them through reporter one time
        try {
          ctx.reporter.fatalError(msg)
        } catch {
          case _: LeonFatalError =>
        }

        hasFatal = true
    }
  }

}
