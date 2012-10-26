package leon

object Main {

  def allPhases: List[LeonPhase[_, _]] = {
    List(
      plugin.ExtractionPhase,
      ArrayTransformation,
      EpsilonElimination,
      ImperativeCodeElimination,
      /*UnitElimination,*/
      FunctionClosure,
      /*FunctionHoisting,*/
      Simplificator,
      synthesis.SynthesisPhase,
      AnalysisPhase
    )
  }

  lazy val allOptions = allPhases.flatMap(_.definedOptions) ++ Set(
      LeonFlagOptionDef ("synthesis", "--synthesis",   "Partial synthesis or choose() constructs"),
      LeonFlagOptionDef ("xlang",     "--xlang",       "Support for extra program constructs (imperative,...)"),
      LeonFlagOptionDef ("parse",     "--parse",       "Checks only whether the program is valid PureScala"),
      LeonValueOptionDef("debug",     "--debug=[1-5]", "Debug level"),
      LeonFlagOptionDef ("help",      "--help",        "This help")
    )

  def displayHelp(reporter: Reporter) {
    reporter.info("usage: leon [--xlang] [--synthesis] [--help] [--debug=<N>] [..] <files>")
    reporter.info("")
    reporter.info("Leon options are:")
    for (opt <- allOptions.toSeq.sortBy(_.name)) {
      reporter.info("   %-20s %s".format(opt.usageOption, opt.usageDesc))
    }
    sys.exit(1)
  }

  def processOptions(reporter: Reporter, args: List[String]) = {
    val phases = allPhases

    val allOptions = this.allOptions

    val allOptionsMap = allOptions.map(o => o.name -> o).toMap

    // Detect unknown options:
    val options = args.filter(_.startsWith("--"))

    val files = args.filterNot(_.startsWith("-"))

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
            reporter.error("Invalid option usage: "+opt)
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
        settings = settings.copy(synthesis = true, xlang = false, analyze = false)
      case LeonFlagOption("xlang") =>
        settings = settings.copy(synthesis = false, xlang = true)
      case LeonFlagOption("parse") =>
        settings = settings.copy(synthesis = false, xlang = false, analyze = false)
      case LeonFlagOption("help") =>
        displayHelp(reporter)
      case _ =>
    }

    LeonContext(settings = settings, reporter = reporter, files = files, options = leonOptions)
  }

  implicit def phaseToPipeline[F, T](phase: LeonPhase[F, T]): Pipeline[F, T] = new PipeCons(phase, new PipeNil())

  def computePipeline(settings: Settings): Pipeline[List[String], Unit] = {
    import purescala.Definitions.Program

    val pipeBegin = phaseToPipeline(plugin.ExtractionPhase)

    val pipeTransforms: Pipeline[Program, Program] =
      if (settings.xlang) {
        ArrayTransformation andThen
        EpsilonElimination andThen
        ImperativeCodeElimination andThen
        FunctionClosure
      } else {
        NoopPhase[Program]()
      }

    val pipeSynthesis: Pipeline[Program, Program]=
      if (settings.synthesis) {
        synthesis.SynthesisPhase
      } else {
        NoopPhase[Program]()
      }

    val pipeAnalysis: Pipeline[Program, Program] =
      if (settings.analyze) {
        AnalysisPhase
      } else {
        NoopPhase[Program]()
      }

    pipeBegin followedBy
    pipeTransforms followedBy
    pipeSynthesis followedBy
    pipeAnalysis andThen
    ExitPhase[Program]()
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
