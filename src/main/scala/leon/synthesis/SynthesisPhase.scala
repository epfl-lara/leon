package leon
package synthesis

import purescala.TreeOps._
import solvers.TrivialSolver
import solvers.z3.{FairZ3Solver,UninterpretedZ3Solver}

import purescala.Trees._
import purescala.ScalaPrinter
import purescala.Definitions.{Program, FunDef}

object SynthesisPhase extends LeonPhase[Program, Program] {
  val name        = "Synthesis"
  val description = "Synthesis"

  override def definedOptions = Set(
    LeonFlagOptionDef( "inplace",    "--inplace",         "Debug level"),
    LeonFlagOptionDef( "parallel",   "--parallel",        "Parallel synthesis search"),
    LeonFlagOptionDef( "derivtrees", "--derivtrees",      "Generate derivation trees"),
    LeonFlagOptionDef( "firstonly",  "--firstonly",       "Stop as soon as one synthesis solution is found"),
    LeonValueOptionDef("timeout",    "--timeout=T",       "Timeout after T seconds when searching for synthesis solutions .."),
    LeonValueOptionDef("functions",  "--functions=f1:f2", "Limit synthesis of choose found within f1,f2,..")
  )

  def run(ctx: LeonContext)(p: Program): Program = {
    val silentContext : LeonContext = ctx.copy(reporter = new SilentReporter)

    val mainSolver = new FairZ3Solver(silentContext)
    mainSolver.setProgram(p)

    val uninterpretedZ3 = new UninterpretedZ3Solver(silentContext)
    uninterpretedZ3.setProgram(p)

    var inPlace                        = false
    var genTrees                       = false
    var firstOnly                      = false
    var parallel                       = false
    var filterFun: Option[Seq[String]] = None 
    var timeoutMs: Option[Long]        = None

    for(opt <- ctx.options) opt match {
      case LeonFlagOption("inplace") =>
        inPlace = true
      case LeonValueOption("functions", ListValue(fs)) =>
        filterFun = Some(fs)
      case LeonValueOption("timeout", t) =>
        try {
          timeoutMs  = Some(t.toLong)
        } catch {
          case _: Throwable => 
        }
      case LeonFlagOption("firstonly") =>
        firstOnly = true
      case LeonFlagOption("parallel") =>
        parallel = true
      case LeonFlagOption("derivtrees") =>
        genTrees = true
      case _ =>
    }

    def synthesizeAll(program: Program): Map[Choose, Solution] = {
      def noop(u:Expr, u2: Expr) = u

      var solutions = Map[Choose, Solution]()

      def actOnChoose(f: FunDef)(e: Expr, a: Expr): Expr = e match {
        case ch @ Choose(vars, pred) =>
          val problem = Problem.fromChoose(ch)
          val synth = new Synthesizer(ctx,
                                      mainSolver,
                                      p,
                                      problem,
                                      Rules.all ++ Heuristics.all,
                                      genTrees,
                                      filterFun.map(_.toSet),
                                      parallel,
                                      firstOnly,
                                      timeoutMs)
          val sol = synth.synthesize()

          solutions += ch -> sol

          a
        case _ =>
          a
      }

      // Look for choose()
      for (f <- program.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) {
        if (filterFun.isEmpty || filterFun.get.contains(f.id.toString)) {
          treeCatamorphism(x => x, noop, actOnChoose(f), f.body.get)
        }
      }

      solutions
    }

    val solutions = synthesizeAll(p)

    // Simplify expressions
    val simplifiers = List[Expr => Expr](
      simplifyTautologies(uninterpretedZ3)(_), 
      simplifyLets _,
      decomposeIfs _,
      patternMatchReconstruction _,
      simplifyTautologies(uninterpretedZ3)(_),
      simplifyLets _
    )

    def simplify(e: Expr): Expr = simplifiers.foldLeft(e){ (x, sim) => sim(x) }

    val chooseToExprs = solutions.map {
      case (ch, sol) => (ch, simplify(sol.toExpr))
    }

    if (inPlace) {
      for (file <- ctx.files) {
        new FileInterface(ctx.reporter, file).updateFile(chooseToExprs)
      }
    } else {
      for ((chs, ex) <- chooseToExprs) {
        ctx.reporter.info("-"*32+" Synthesis of: "+"-"*32)
        ctx.reporter.info(chs)
        ctx.reporter.info("-"*35+" Result: "+"-"*35)
        ctx.reporter.info(ScalaPrinter(ex))
        ctx.reporter.info("")
      }
    }

    p
  }


}
