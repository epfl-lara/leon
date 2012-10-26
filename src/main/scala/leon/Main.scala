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
      LeonFlagOptionDef ("synthesis",    "--synthesis",   "Partial synthesis or choose() constructs"),
      LeonFlagOptionDef ("xlang",        "--xlang",       "Support for extra program constructs (imperative,...)"),
      LeonFlagOptionDef ("parse",        "--parse",       "Checks only whether the program is valid PureScala"),
      LeonValueOptionDef("debug",        "--debug=[1-5]", "Debug level"),
      LeonFlagOptionDef ("help",         "--help",        "This help")

      //  Unimplemented Options:
      //
      //  LeonFlagOptionDef("uniqid",        "--uniqid",             "When pretty-printing purescala trees, show identifiers IDs"),
      //  LeonValueOptionDef("extensions",   "--extensions=ex1:...", "Specifies a list of qualified class names of extensions to be loaded"),
      //  LeonFlagOptionDef("nodefaults",    "--nodefaults",         "Runs only the analyses provided by the extensions"),
      //  LeonValueOptionDef("functions",    "--functions=fun1:...", "Only generates verification conditions for the specified functions"),
      //  LeonFlagOptionDef("unrolling",     "--unrolling=[0,1,2]",  "Unrolling depth for recursive functions" ),
      //  LeonFlagOptionDef("axioms",        "--axioms",             "Generate simple forall axioms for recursive functions when possible" ),
      //  LeonFlagOptionDef("tolerant",      "--tolerant",           "Silently extracts non-pure function bodies as ''unknown''"),
      //  LeonFlagOptionDef("bapa",          "--bapa",               "Use BAPA Z3 extension (incompatible with many other things)"),
      //  LeonFlagOptionDef("impure",        "--impure",             "Generate testcases only for impure functions"),
      //  LeonValueOptionDef("testcases",    "--testcases=[1,2]",    "Number of testcases to generate per function"),
      //  LeonValueOptionDef("testbounds",   "--testbounds=l:u",     "Lower and upper bounds for integers in recursive datatypes"),
      //  LeonValueOptionDef("timeout",      "--timeout=N",          "Sets a timeout of N seconds"),
      //  LeonFlagOptionDef("XP",            "--XP",                 "Enable weird transformations and other bug-producing features"),
      //  LeonFlagOptionDef("BV",            "--BV",                 "Use bit-vectors for integers"),
      //  LeonFlagOptionDef("prune",         "--prune",              "Use additional SMT queries to rule out some unrollings"),
      //  LeonFlagOptionDef("cores",         "--cores",              "Use UNSAT cores in the unrolling/refinement step"),
      //  LeonFlagOptionDef("quickcheck",    "--quickcheck",         "Use QuickCheck-like random search"),
      //  LeonFlagOptionDef("parallel",      "--parallel",           "Run all solvers in parallel"),
      //  LeonFlagOptionDef("noLuckyTests",  "--noLuckyTests",       "Do not perform additional tests to potentially find models early"),
      //  LeonFlagOptionDef("noverifymodel", "--noverifymodel",      "Do not verify the correctness of models returned by Z3"),
      //  LeonValueOptionDef("tags",         "--tags=t1:...",        "Filter out debug information that are not of one of the given tags"),
      //  LeonFlagOptionDef("oneline",       "--oneline",            "Reduce the output to a single line: valid if all properties were valid, invalid if at least one is invalid, unknown else")
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
