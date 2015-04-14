/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import leon.utils._
import solvers.SolverFactory

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
      repair.RepairPhase
    )
  }

  // Add whatever you need here.
  lazy val allComponents : Set[LeonComponent] = allPhases.toSet ++ Set(
    new solvers.z3.FairZ3Component{}
  )

  lazy val topLevelOptions : Set[LeonOptionDef] = Set(
      LeonFlagOptionDef ("termination", "--termination",        "Check program termination"),
      LeonFlagOptionDef ("repair",      "--repair",             "Repair selected functions"),
      LeonFlagOptionDef ("synthesis",   "--synthesis",          "Partial synthesis of choose() constructs"),
      LeonFlagOptionDef ("xlang",       "--xlang",              "Support for extra program constructs (imperative,...)"),
      LeonFlagOptionDef ("watch",       "--watch",              "Rerun pipeline when file changes"),
      LeonValueOptionDef("solvers",     "--solvers=s1,s2",      "Use solvers s1 and s2 (fairz3,enum,smt-z3,smt-cvc4)"),
      LeonValueOptionDef("debug",       "--debug=<sections..>", "Enables specific messages"),
      LeonFlagOptionDef ("noop",        "--noop",               "No operation performed, just output program"),
      LeonFlagOptionDef ("help",        "--help",               "Show help")
    )

  lazy val allOptions = allComponents.flatMap(_.definedOptions) ++ topLevelOptions

  def displayHelp(reporter: Reporter, error: Boolean) {
    reporter.info("usage: leon [--xlang] [--termination] [--synthesis] [--help] [--debug=<N>] [..] <files>")
    reporter.info("")
    for (opt <- topLevelOptions.toSeq.sortBy(_.name)) {
      reporter.info(f"${opt.usageOption}%-20s ${opt.usageDesc}")
    }
    reporter.info("(By default, Leon verifies PureScala programs.)")
    reporter.info("")
    reporter.info("Additional options, by component:")

    for (c <- allComponents.toSeq.sortBy(_.name) if c.definedOptions.nonEmpty) {
      reporter.info("")
      reporter.info(s"${c.name} (${c.description})")
      for(opt <- c.definedOptions.toSeq.sortBy(_.name)) {
        // there is a non-breaking space at the beginning of the string :)
        reporter.info(f"${opt.usageOption}%-20s ${opt.usageDesc}")
      }
    }
    exit(error)
  }

  private def exit(error: Boolean) = sys.exit(if (error) 1 else 0)

  def processOptions(args: Seq[String]): LeonContext = {

    val initReporter = new DefaultReporter(Settings())

    val allOptions = this.allOptions

    val allOptionsMap = allOptions.map(o => o.name -> o).toMap

    // Detect unknown options:
    val options = args.filter(_.startsWith("--"))

    val files = args.filterNot(_.startsWith("-")).map(new java.io.File(_))

    def valueToFlag(s: String) = s match {
      case "on"  | "true"  | "yes" => Some(true)
      case "off" | "false" | "no"  => Some(false)
      case _ => None
    }

    var optionsValues: Map[LeonOptionDef, String] = allOptions.flatMap{
      case fod: LeonFlagOptionDef =>
        Some((fod, if (fod.default) "on" else "off"))
      case vod: LeonValueOptionDef =>
        vod.default.map(d =>
          (vod, d)
        )
    }.toMap

    for (opt <- options) {
      val (name, value) = opt.substring(2, opt.length).split("=", 2).toList match {
        case List(name, value) =>
          (name, Some(value))
        case List(name) =>
          (name, None)
      }

      val optV = allOptionsMap.get(name) match {
        case Some(fod: LeonFlagOptionDef) =>
          value.orElse(Some("on"))

        case Some(vod: LeonValueOptionDef) =>
          value.orElse(vod.flagValue)

        case _ =>
          None
      }

      if (allOptionsMap contains name) {
        optV.foreach { v =>
          optionsValues +=  allOptionsMap(name) -> v
        }
      } else {
        initReporter.fatalError("'"+name+"' is not a valid option. See 'leon --help'")
      }
    }

    val leonOptions = optionsValues.flatMap {
      case (fod: LeonFlagOptionDef, value) =>
        valueToFlag(value) match {
          case Some(v) =>
            Some(LeonFlagOption(fod.name, v))
          case None =>
            initReporter.error("Invalid option usage: --"+fod.name+"="+value)
            displayHelp(initReporter, error=true)
            None
        }
      case (vod: LeonValueOptionDef, value) =>
        Some(LeonValueOption(vod.name, value))
    }.toSeq

    var settings  = Settings()

    // Process options we understand:
    for(opt <- leonOptions) opt match {
      case LeonFlagOption("termination", value) =>
        settings = settings.copy(termination = value)
      case LeonFlagOption("repair", value) =>
        settings = settings.copy(repair = value)
      case LeonFlagOption("synthesis", value) =>
        settings = settings.copy(synthesis = value)
      case LeonFlagOption("xlang", value) =>
        settings = settings.copy(xlang = value)
      case LeonValueOption("solvers", ListValue(ss)) =>
        val available = SolverFactory.definedSolvers
        val unknown = ss.toSet -- available
        if (unknown.nonEmpty) {
          initReporter.error("Unknown solver(s): "+unknown.mkString(", ")+" (Available: "+available.mkString(", ")+")")
        }
        settings = settings.copy(selectedSolvers = ss.toSet)

      case LeonValueOption("debug", ListValue(sections)) =>
        val debugSections = sections.flatMap { s =>
          if (s == "all") {
            DebugSections.all
          } else {
            DebugSections.all.find(_.name == s) match {
              case Some(rs) =>
                Some(rs)
              case None =>
                initReporter.error("Section "+s+" not found, available: "+DebugSections.all.map(_.name).mkString(", "))
                None
            }
          }
        }
        settings = settings.copy(debugSections = debugSections.toSet)
      case LeonFlagOption("noop", true) =>
        settings = settings.copy(verify = false)
      case LeonFlagOption("help", true) =>
        displayHelp(initReporter, error = false)
      case _ =>
    }

    // Create a new reporter taking settings into account
    val reporter = new DefaultReporter(settings)

    reporter.whenDebug(DebugSectionOptions) { debug =>

      debug("Options considered by Leon:")
      for (lo <- leonOptions) lo match {
        case LeonFlagOption(name, v) =>
          debug("  --"+name+"="+(if(v) "on" else "off"))
        case LeonValueOption(name, v) =>
          debug("  --"+name+"="+v)

      }
    }

    val intManager = new InterruptManager(reporter)

    LeonContext(settings = settings,
                reporter = reporter,
                files = files,
                options = leonOptions,
                interruptManager = intManager)
  }

  def computePipeline(settings: Settings): Pipeline[List[String], Any] = {
    import purescala.Definitions.Program
    import purescala.{FunctionClosure, RestoreMethods}
    import utils.FileOutputPhase
    import frontends.scalac.ExtractionPhase
    import synthesis.SynthesisPhase
    import termination.TerminationPhase
    import xlang.XLangAnalysisPhase
    import verification.AnalysisPhase
    import repair.RepairPhase

    val pipeSanityCheck : Pipeline[Program, Program] = 
      if(!settings.xlang)
        xlang.NoXLangFeaturesChecking
      else
        NoopPhase()

    val pipeBegin : Pipeline[List[String],Program] =
      ExtractionPhase andThen
      PreprocessingPhase andThen
      pipeSanityCheck

    val pipeProcess: Pipeline[Program, Any] = {
      if (settings.synthesis) {
        SynthesisPhase
      } else if (settings.repair) {
        RepairPhase
      } else if (settings.termination) {
        TerminationPhase
      } else if (settings.xlang) {
        XLangAnalysisPhase
      } else if (settings.verify) {
        FunctionClosure andThen AnalysisPhase
      } else {
        RestoreMethods andThen FileOutputPhase
      }
    }

    pipeBegin andThen
    pipeProcess
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
          new DefaultReporter(Settings()).fatalError(msg)
        } catch {
          case _: LeonFatalError =>
        }

        exit(error=true)
    }

    ctx.interruptManager.registerSignalHandler()

    val doWatch = ctx.options.exists {
      case LeonFlagOption("watch", value) => value
      case _ => false
    }

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
    val ctx = ctx0.copy(reporter = new DefaultReporter(ctx0.settings))

    try {
      // Compute leon pipeline
      val pipeline = computePipeline(ctx.settings)

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
