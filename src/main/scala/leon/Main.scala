/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import leon.utils._

object Main {

  lazy val allPhases: List[LeonPhase[_, _]] = {
    List(
      plugin.ExtractionPhase,
      SubtypingPhase,
      xlang.ArrayTransformation,
      xlang.EpsilonElimination,
      xlang.ImperativeCodeElimination,
      purescala.FunctionClosure,
      xlang.XlangAnalysisPhase,
      synthesis.SynthesisPhase,
      termination.TerminationPhase,
      verification.AnalysisPhase
    )
  }

  // Add whatever you need here.
  lazy val allComponents : Set[LeonComponent] = allPhases.toSet ++ Set(
    new solvers.z3.FairZ3Component{}
  )

  lazy val topLevelOptions : Set[LeonOptionDef] = Set(
      LeonFlagOptionDef ("termination", "--termination",        "Check program termination"),
      LeonFlagOptionDef ("synthesis",   "--synthesis",          "Partial synthesis of choose() constructs"),
      LeonFlagOptionDef ("xlang",       "--xlang",              "Support for extra program constructs (imperative,...)"),
      LeonValueOptionDef("debug",       "--debug=<sections..>", "Enables specific messages"),
      LeonFlagOptionDef ("help",        "--help",               "Show help")
    )

  lazy val allOptions = allComponents.flatMap(_.definedOptions) ++ topLevelOptions

  def displayHelp(reporter: Reporter) {
    reporter.info("usage: leon [--xlang] [--termination] [--synthesis] [--help] [--debug=<N>] [..] <files>")
    reporter.info("")
    for (opt <- topLevelOptions.toSeq.sortBy(_.name)) {
      reporter.info("%-20s %s".format(opt.usageOption, opt.usageDesc))
    }
    reporter.info("(By default, Leon verifies PureScala programs.)")
    reporter.info("")
    reporter.info("Additional options, by component:")

    for (c <- allComponents.toSeq.sortBy(_.name) if !c.definedOptions.isEmpty) {
      reporter.info("")
      reporter.info("%s (%s)".format(c.name, c.description))
      for(opt <- c.definedOptions.toSeq.sortBy(_.name)) {
        // there is a non-breaking space at the beginning of the string :)
        reporter.info("%-20s %s".format(opt.usageOption, opt.usageDesc))
      }
    }
    sys.exit(1)
  }

  def processOptions(args: Seq[String]): LeonContext = {
    val phases = allPhases

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
            displayHelp(initReporter)
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
      case LeonFlagOption("synthesis", value) =>
        settings = settings.copy(synthesis = value)
      case LeonFlagOption("xlang", value) =>
        settings = settings.copy(xlang = value)
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
      case LeonFlagOption("help", true) =>
        displayHelp(initReporter)
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

    intManager.registerSignalHandler()

    LeonContext(settings = settings,
                reporter = reporter,
                files = files,
                options = leonOptions,
                interruptManager = intManager)
  }

  def computePipeline(settings: Settings): Pipeline[List[String], Any] = {
    import purescala.Definitions.Program

    val pipeBegin : Pipeline[List[String],Program] = plugin.ExtractionPhase andThen SubtypingPhase

    val pipeProcess: Pipeline[Program, Any] =
      if (settings.synthesis) {
        synthesis.SynthesisPhase
      } else if (settings.termination) {
        termination.TerminationPhase
      } else if (settings.xlang) {
        xlang.XlangAnalysisPhase
      } else if (settings.verify) {
        verification.AnalysisPhase
      } else {
        NoopPhase()
      }

    pipeBegin andThen
    pipeProcess
  }

  def main(args : Array[String]) {
    try {
      // Process options
      val timer     = new Timer().start

      val ctx = processOptions(args.toList)

      ctx.timers.get("Leon Opts") += timer

      // Compute leon pipeline
      val pipeline = computePipeline(ctx.settings)

      timer.restart

      // Run pipeline
      pipeline.run(ctx)(args.toList) match {
        case report: verification.VerificationReport =>
          ctx.reporter.info(report.summaryString)

        case report: termination.TerminationReport =>
          ctx.reporter.info(report.summaryString)

        case _ =>
      }

      ctx.timers.get("Leon Run") += timer

      ctx.reporter.whenDebug(DebugSectionTimers) { debug =>
        debug("-"*80)
        debug("Times:")
        debug("-"*80)
        for ((name, swc) <- ctx.timers.getAll.toSeq.sortBy(_._1)) {
          debug(swc.toString)
        }
        debug("-"*80)
      }

    } catch {
      case LeonFatalError() => sys.exit(1)
    }
  }
}
