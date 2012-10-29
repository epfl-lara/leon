package leon
package synthesis

import purescala.TreeOps._
import solvers.TrivialSolver
import solvers.z3.{FairZ3Solver,UninterpretedZ3Solver}

import purescala.Trees.Expr
import purescala.ScalaPrinter
import purescala.Definitions.Program

object SynthesisPhase extends LeonPhase[Program, Program] {
  val name        = "Synthesis"
  val description = "Synthesis"

  override def definedOptions = Set(
    LeonFlagOptionDef("inplace", "--inplace",           "Debug level"),
    LeonFlagOptionDef("derivtrees", "--derivtrees",     "Generate derivation trees")
  )

  def run(ctx: LeonContext)(p: Program): Program = {
    val quietReporter = new QuietReporter
    val solvers  = List(
      new TrivialSolver(quietReporter),
      new FairZ3Solver(quietReporter)
    )
    val uninterpretedZ3 = new UninterpretedZ3Solver(quietReporter)
    uninterpretedZ3.setProgram(p)

    var inPlace  = false
    var genTrees = false
    for(opt <- ctx.options) opt match {
      case LeonFlagOption("inplace") =>
        inPlace = true
      case LeonFlagOption("derivtrees") =>
        genTrees = true
      case _ =>
    }

    val synth = new Synthesizer(ctx.reporter, solvers, genTrees)
    val solutions = synth.synthesizeAll(p)


    // Simplify expressions
    val simplifiers = List[Expr => Expr](
      simplifyTautologies(uninterpretedZ3)(_), 
      simplifyLets _,
      decomposeIfs _
    )

    val chooseToExprs = solutions.mapValues(sol => simplifiers.foldLeft(sol.toExpr){ (x, sim) => sim(x) })

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
      }
    }

    p
  }

}
