/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import leon.utils._

object Main {

  lazy val allPhases: List[LeonPhase[_, _]] = {
    List(
      frontends.scalac.ExtractionPhase,
      utils.TypingPhase,
      FileOutputPhase,
      ScopingPhase,
      purescala.RestoreMethods,
      xlang.ArrayTransformation,
      xlang.EpsilonElimination,
      xlang.ImperativeCodeElimination,
      purescala.FunctionClosure,
      xlang.XLangAnalysisPhase,
      synthesis.SynthesisPhase,
      termination.TerminationPhase,
      verification.AnalysisPhase,
      repair.RepairPhase,
      evaluators.EvaluationPhase
    )
  }

  // Add whatever you need here.
  lazy val allComponents : Set[LeonComponent] = allPhases.toSet ++ Set(
    solvers.z3.FairZ3Component, MainComponent, SharedOptions, solvers.smtlib.SMTLIBCVC4Component
  )

  object MainComponent extends LeonComponent {
    val name = "main"
    val description = "Options that determine the feature of Leon to be used (mutually exclusive). Default: verify"

    val optTermination = LeonFlagOptionDef("termination", "Check program termination",                             false)
    val optRepair      = LeonFlagOptionDef("repair",      "Repair selected functions",                             false)
    val optSynthesis   = LeonFlagOptionDef("synthesis",   "Partial synthesis of choose() constructs",              false)
    val optXLang       = LeonFlagOptionDef("xlang",       "Support for extra program constructs (imperative,...)", false)
    val optNoop        = LeonFlagOptionDef("noop",        "No operation performed, just output program",           false)
    val optVerify      = LeonFlagOptionDef("verify",      "Verify function contracts",                             true )
    val optHelp        = LeonFlagOptionDef("help",        "Show help message",                                     false)
    val optEval        = LeonFlagOptionDef("eval",        "Evaluate ground functions",                             false)

    override val definedOptions: Set[LeonOptionDef[Any]] =
      Set(optTermination, optRepair, optSynthesis, optXLang, optNoop, optHelp, optVerify, optEval)

  }

  lazy val allOptions: Set[LeonOptionDef[Any]] = allComponents.flatMap(_.definedOptions)

  def displayHelp(reporter: Reporter, error: Boolean) = {
    reporter.info(MainComponent.description)
    for (opt <- MainComponent.definedOptions.toSeq.sortBy(_.name)) {
      reporter.info(opt.helpString)
    }
    reporter.info("")

    reporter.info("Additional top-level options")
    for (opt <- SharedOptions.definedOptions.toSeq.sortBy(_.name)) {
      reporter.info(opt.helpString)
    }
    reporter.info("")
      
    reporter.info("Additional options, by component:")

    for (c <- (allComponents - MainComponent - SharedOptions).toSeq.sortBy(_.name) if c.definedOptions.nonEmpty) {
      reporter.info("")
      reporter.info(s"${c.name} (${c.description})")
      for(opt <- c.definedOptions.toSeq.sortBy(_.name)) {
        // there is a non-breaking space at the beginning of the string :)
        reporter.info(opt.helpString)
      }
    }
    exit(error)
  }

  def displayVersion(reporter: Reporter) = {
    reporter.info("Leon verification and synthesis tool (http://leon.epfl.ch/)")
    reporter.info("")
  }

  private def exit(error: Boolean) = sys.exit(if (error) 1 else 0)

  def processOptions(args: Seq[String]): LeonContext = {

    val initReporter = new DefaultReporter(Set())

    val allOptions: Set[LeonOptionDef[Any]] = this.allOptions

    val options = args.filter(_.startsWith("--")).toSet

    val files = args.filterNot(_.startsWith("-")).map(new java.io.File(_))

    val leonOptions: Set[LeonOption[Any]] = options.map { opt =>
      val (name, value) = try {
        OptionsHelpers.nameValue(opt)
      } catch {
        case _ : IllegalArgumentException =>
          initReporter.fatalError(
            s"Malformed option $opt. Options should have the form --name or --name=value"
          )
      }
      // Find respective LeonOptionDef, or report an unknown option
      val df = allOptions.find(_. name == name).getOrElse{
        initReporter.error(s"Unknown option: $name")
        displayHelp(initReporter, error = true)
      }
      df.parse(value)(initReporter)
    }

    val reporter = new DefaultReporter(
      leonOptions.collectFirst {
        case LeonOption(SharedOptions.optDebug, sections) => sections.asInstanceOf[Set[DebugSection]]
      }.getOrElse(Set[DebugSection]())
    )

    reporter.whenDebug(DebugSectionOptions) { debug =>
      debug("Options considered by Leon:")
      for (lo <- leonOptions) debug(lo.toString)
    }

    LeonContext(
      reporter = reporter,
      files = files,
      options = leonOptions.toSeq,
      interruptManager = new InterruptManager(reporter)
    )
  }

  def computePipeline(ctx: LeonContext): Pipeline[List[String], Any] = {

    import purescala.Definitions.Program
    import purescala.{FunctionClosure, RestoreMethods}
    import utils.FileOutputPhase
    import frontends.scalac.ExtractionPhase
    import synthesis.SynthesisPhase
    import termination.TerminationPhase
    import xlang.XLangAnalysisPhase
    import verification.AnalysisPhase
    import repair.RepairPhase
    import evaluators.EvaluationPhase
    import MainComponent._

    val helpF        = ctx.findOptionOrDefault(optHelp)
    val noopF        = ctx.findOptionOrDefault(optNoop)
    val synthesisF   = ctx.findOptionOrDefault(optSynthesis)
    val xlangF       = ctx.findOptionOrDefault(optXLang)
    val repairF      = ctx.findOptionOrDefault(optRepair)
    val terminationF = ctx.findOptionOrDefault(optTermination)
    val verifyF      = ctx.findOptionOrDefault(optVerify)
    val evalF        = ctx.findOptionOrDefault(optEval)

    def debugTrees(title: String): LeonPhase[Program, Program] = {
      if (ctx.reporter.isDebugEnabled(DebugSectionTrees)) {
        PrintTreePhase(title)
      } else {
        NoopPhase[Program]
      }
    }

    if (helpF) {
      displayVersion(ctx.reporter)
      displayHelp(ctx.reporter, error = false)
    } else {
      val pipeBegin: Pipeline[List[String], Program] =
        if (xlangF)
          ExtractionPhase andThen
          debugTrees("Program after extraction") andThen
          PreprocessingPhase andThen
          debugTrees("Program after pre-processing")
        else
          ExtractionPhase andThen
          debugTrees("Program after extraction") andThen
          PreprocessingPhase andThen
          debugTrees("Program after pre-processing")
          xlang.NoXLangFeaturesChecking

      val pipeProcess: Pipeline[Program, Any] = {
        if (noopF) RestoreMethods andThen FileOutputPhase
        else if (synthesisF) SynthesisPhase
        else if (repairF) RepairPhase
        else if (terminationF) TerminationPhase
        else if (xlangF) XLangAnalysisPhase
        else if (evalF) EvaluationPhase
        else if (verifyF) FunctionClosure andThen AnalysisPhase
        else    NoopPhase()
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
        exit(error=true)

      case LeonFatalError(Some(msg)) =>
        // For the special case of fatal errors not sent though Reporter, we
        // send them through reporter one time
        try {
          new DefaultReporter(Set()).fatalError(msg)
        } catch {
          case _: LeonFatalError =>
        }

        exit(error=true)
    }

    ctx.interruptManager.registerSignalHandler()

    val doWatch = ctx.findOptionOrDefault(SharedOptions.optWatch)

    if (doWatch) {
      val watcher = new FilesWatcher(ctx, ctx.files)
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
      pipeline.run(ctx)(args.toList) match {
        case report: verification.VerificationReport =>
          ctx.reporter.info(report.summaryString)

        case report: termination.TerminationReport =>
          ctx.reporter.info(report.summaryString)

        case _ =>
      }

      timer.stop()

      ctx.reporter.whenDebug(DebugSectionTimers) { debug =>
        ctx.timers.outputTable(debug)
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
