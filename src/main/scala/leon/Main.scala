package leon

object Main {

  lazy val allPhases: List[LeonPhase[_, _]] = {
    List(
      plugin.ExtractionPhase,
      xlang.ArrayTransformation,
      xlang.EpsilonElimination,
      xlang.ImperativeCodeElimination,
      xlang.FunctionClosure,
      synthesis.SynthesisPhase,
      verification.AnalysisPhase
    )
  }

  // Add whatever you need here.
  lazy val allComponents : Set[LeonComponent] = allPhases.toSet ++ Set(
    // It's a little unfortunate that we need to build one...
    new solvers.z3.FairZ3Solver(LeonContext())
  )

  lazy val topLevelOptions : Set[LeonOptionDef] = Set(
      LeonFlagOptionDef ("synthesis",    "--synthesis",   "Partial synthesis of choose() constructs"),
      LeonFlagOptionDef ("xlang",        "--xlang",       "Support for extra program constructs (imperative,...)"),
      LeonFlagOptionDef ("parse",        "--parse",       "Checks only whether the program is valid PureScala"),
      LeonValueOptionDef("debug",        "--debug=[1-5]", "Debug level"),
      LeonFlagOptionDef ("help",         "--help",        "Show help")

      //  Unimplemented Options:
      //
      //  LeonFlagOptionDef("uniqid",        "--uniqid",             "When pretty-printing purescala trees, show identifiers IDs"),
      //  LeonFlagOptionDef("tolerant",      "--tolerant",           "Silently extracts non-pure function bodies as ''unknown''"),
    )

  lazy val allOptions = allComponents.flatMap(_.definedOptions) ++ topLevelOptions

  def displayHelp(reporter: Reporter) {
    reporter.info("usage: leon [--xlang] [--synthesis] [--help] [--debug=<N>] [..] <files>")
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

  def processOptions(reporter: Reporter, args: List[String]) = {
    val phases = allPhases

    val allOptions = this.allOptions

    val allOptionsMap = allOptions.map(o => o.name -> o).toMap

    // Detect unknown options:
    val options = args.filter(_.startsWith("--"))

    val files = args.filterNot(_.startsWith("-")).map(new java.io.File(_))

    val leonOptions = options.flatMap { opt =>
      val leonOpt: LeonOption = opt.substring(2, opt.length).split("=", 2).toList match {
        case List(name, value) =>
          LeonValueOption(name, value)
        case List(name) => name
          LeonFlagOption(name)
        case _ =>
          reporter.fatalError("Woot?")
      }

      if (allOptionsMap contains leonOpt.name) {
        (allOptionsMap(leonOpt.name).isFlag, leonOpt) match {
          case (true,  LeonFlagOption(name)) =>
            Some(leonOpt)
          case (false, LeonValueOption(name, value)) =>
            Some(leonOpt)
          case _ =>
            reporter.error("Invalid option usage: " + opt)
            displayHelp(reporter)
            None
        }
      } else {
        reporter.error("leon: '"+opt+"' is not a valid option. See 'leon --help'")
        None
      }
    }

    var settings  = Settings()

    // Process options we understand:
    for(opt <- leonOptions) opt match {
      case LeonFlagOption("synthesis") =>
        settings = settings.copy(synthesis = true, xlang = false, verify = false)
      case LeonFlagOption("xlang") =>
        settings = settings.copy(synthesis = false, xlang = true)
      case LeonFlagOption("parse") =>
        settings = settings.copy(synthesis = false, xlang = false, verify = false)
      case LeonFlagOption("help") =>
        displayHelp(reporter)
      case _ =>
    }

    LeonContext(settings = settings, reporter = reporter, files = files, options = leonOptions)
  }

  def computePipeline(settings: Settings): Pipeline[List[String], Any] = {
    import purescala.Definitions.Program

    val pipeBegin : Pipeline[List[String],Program] = plugin.ExtractionPhase

    val pipeTransforms: Pipeline[Program, Program] =
      if (settings.xlang) {
        xlang.ArrayTransformation andThen
        xlang.EpsilonElimination andThen
        xlang.ImperativeCodeElimination andThen
        xlang.FunctionClosure
      } else {
        NoopPhase()
      }

    val pipeSynthesis: Pipeline[Program, Program]=
      if (settings.synthesis) {
        synthesis.SynthesisPhase
      } else {
        NoopPhase()
      }

    val pipeVerify: Pipeline[Program, Any] =
      if (settings.verify) {
        verification.AnalysisPhase
      } else {
        NoopPhase()
      }

    pipeBegin andThen
    pipeTransforms andThen
    pipeSynthesis andThen
    pipeVerify
  }

  def main(args : Array[String]) {
    val reporter = new DefaultReporter()

    // Process options
    val ctx = processOptions(reporter, args.toList)

    // Compute leon pipeline
    val pipeline = computePipeline(ctx.settings)

    // Run pipeline
    pipeline.run(ctx)(args.toList)
  }
}
