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
    LeonValueOptionDef("costmodel",  "--costmodel=cm",    "Use a specific cost model for this search"),
    LeonValueOptionDef("functions",  "--functions=f1:f2", "Limit synthesis of choose found within f1,f2,..")
  )

  def run(ctx: LeonContext)(p: Program): Program = {
    val silentContext : LeonContext = ctx.copy(reporter = new SilentReporter)

    val mainSolver = new FairZ3Solver(silentContext)
    mainSolver.setProgram(p)

    val uninterpretedZ3 = new UninterpretedZ3Solver(silentContext)
    uninterpretedZ3.setProgram(p)

    var options = SynthesizerOptions()
    var inPlace                        = false

    for(opt <- ctx.options) opt match {
      case LeonFlagOption("inplace") =>
        inPlace = true
      case LeonValueOption("functions", ListValue(fs)) =>
        options = options.copy(filterFuns = Some(fs.toSet))
      case LeonValueOption("costmodel", cm) =>
        CostModel.all.find(_.name.toLowerCase == cm.toLowerCase) match {
          case Some(model) =>
            options = options.copy(costModel = model)
          case None =>
            ctx.reporter.fatalError("Unknown cost model: "+cm)
        }
      case LeonValueOption("timeout", t) =>
        try {
          options = options.copy(timeoutMs  = Some(t.toLong))
        } catch {
          case _: Throwable => 
        }
      case LeonFlagOption("firstonly") =>
        options = options.copy(firstOnly = true)
      case LeonFlagOption("parallel") =>
        options = options.copy(parallel = true)
      case LeonFlagOption("derivtrees") =>
        options = options.copy(generateDerivationTrees = true)
      case _ =>
    }

    def synthesizeAll(program: Program): Map[Choose, (FunDef, Solution)] = {
      def noop(u:Expr, u2: Expr) = u

      var solutions = Map[Choose, (FunDef, Solution)]()

      def actOnChoose(f: FunDef)(e: Expr, a: Expr): Expr = e match {
        case ch @ Choose(vars, pred) =>
          val problem = Problem.fromChoose(ch)
          val synth = new Synthesizer(ctx,
                                      mainSolver,
                                      p,
                                      problem,
                                      Rules.all ++ Heuristics.all,
                                      options)
          val sol = synth.synthesize()

          solutions += ch -> (f, sol._1)

          a
        case _ =>
          a
      }

      // Look for choose()
      for (f <- program.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) {
        if (options.filterFuns.isEmpty || options.filterFuns.get.contains(f.id.toString)) {
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
      case (ch, (fd, sol)) => (ch, (fd, simplify(sol.toExpr)))
    }

    if (inPlace) {
      for (file <- ctx.files) {
        new FileInterface(ctx.reporter, file).updateFile(chooseToExprs.mapValues(_._2))
      }
    } else {
      for ((chs, (fd, ex)) <- chooseToExprs) {
        ctx.reporter.info("-"*32+" In "+fd.id.toString+", synthesis of: "+"-"*32)
        ctx.reporter.info(chs)
        ctx.reporter.info("-"*35+" Result: "+"-"*35)
        ctx.reporter.info(ScalaPrinter(ex))
        ctx.reporter.info("")
      }
    }

    p
  }


}
