package leon
package invariant.engine

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import solvers._
import java.io._
import verification.VerificationReport
import verification.VC
import scala.util.control.Breaks._
import invariant.templateSolvers._
import invariant.factories._
import invariant.util._
import invariant.util.Util._
import invariant.structure._
import invariant.structure.FunctionUtils._
import leon.invariant.factories.TemplateFactory

/**
 * @author ravi
 * This phase performs automatic invariant inference.
 * TODO: should time be implicitly made positive
 */
class InferenceEngine(ctx: InferenceContext) {

  def run(): InferenceReport = {
    val reporter = ctx.reporter
    val program = ctx.program
    reporter.info("Running Inference Engine...")

    //register a shutdownhook
    if (ctx.dumpStats) {
      sys.ShutdownHookThread({ dumpStats(ctx.statsSuffix) })
    }
    val t1 = System.currentTimeMillis()
    //compute functions to analyze by sorting based on topological order (this is an ascending topological order)
    val callgraph = CallGraphUtil.constructCallGraph(program, withTemplates = true)
    val functionsToAnalyze = if (ctx.modularlyAnalyze) {
      callgraph.topologicalOrder
    } else {
      callgraph.topologicalOrder.reverse
    }
    //reporter.info("Analysis Order: " + functionsToAnalyze.map(_.id))
    var results: Map[FunDef, InferenceCondition] = null
    if (!ctx.useCegis) {
      results = analyseProgram(functionsToAnalyze)
      //println("Inferrence did not succeeded for functions: "+functionsToAnalyze.filterNot(succeededFuncs.contains _).map(_.id))
    } else {
      var remFuncs = functionsToAnalyze
      var b = 200
      var maxCegisBound = 200
      breakable {
        while (b <= maxCegisBound) {
          Stats.updateCumStats(1, "CegisBoundsTried")
          val succeededFuncs = analyseProgram(remFuncs)
          remFuncs = remFuncs.filterNot(succeededFuncs.contains _)
          if (remFuncs.isEmpty) break;
          b += 5 //increase bounds in steps of 5
        }
        //println("Inferrence did not succeeded for functions: " + remFuncs.map(_.id))
      }
    }
    val t2 = System.currentTimeMillis()
    Stats.updateCumTime(t2 - t1, "TotalTime")
    //dump stats
    if (ctx.dumpStats) {
      reporter.info("- Dumping statistics")
      dumpStats(ctx.statsSuffix)
    }
    new InferenceReport(program, results.map(pair => {
      val (fd, ic) = pair
      (fd -> List[VC](ic))
    }))(ctx)
  }

  def dumpStats(statsSuffix: String) = {
    //pick the module id.
    val modid = ctx.program.modules.last.id
    val pw = new PrintWriter(modid + statsSuffix + ".txt")
    Stats.dumpStats(pw)
    SpecificStats.dumpOutputs(pw)
    if (ctx.tightBounds) {
      SpecificStats.dumpMinimizationStats(pw)
    }
  }

  /**
   * Returns map from analyzed functions to their inference conditions.
   * TODO: use function names in inference conditions, so that
   * we an get rid of dependence on origFd in many places.
   */
  def analyseProgram(functionsToAnalyze: Seq[FunDef]): Map[FunDef, InferenceCondition] = {
    val reporter = ctx.reporter
    val funToTmpl =
      if (ctx.autoInference) {
        //A template generator that generates templates for the functions (here we are generating templates by enumeration)
        val tempFactory = new TemplateFactory(Some(new TemplateEnumerator(ctx)), ctx.program, ctx.reporter)
        ctx.program.definedFunctions.map(fd => fd -> getOrCreateTemplateForFun(fd)).toMap
      } else
        ctx.program.definedFunctions.collect { case fd if fd.hasTemplate => fd -> fd.getTemplate }.toMap
    val progWithTemplates = assignTemplateAndCojoinPost(funToTmpl, ctx.program)
    var analyzedSet = Map[FunDef, InferenceCondition]()
    functionsToAnalyze.filterNot((fd) => {
      (fd.annotations contains "verified") ||
        (fd.annotations contains "library") ||
        (fd.annotations contains "theoryop")
    }).foldLeft(progWithTemplates) { (prog, origFun) =>

      val funDef = functionByName(origFun.id.name, prog).get
      reporter.info("- considering function " + funDef.id.name + "...")

      //skip the function if it has been analyzed
      if (!analyzedSet.contains(origFun)) {
        if (funDef.hasBody && funDef.hasPostcondition) {
          val currCtx = ctx.copy(program = prog)
          // for stats
          Stats.updateCounter(1, "procs")
          val solver =
            if (funDef.annotations.contains("compose")) //compositional inference ?
              new CompositionalTimeBoundSolver(currCtx, funDef)
            else
              new UnfoldingTemplateSolver(currCtx, funDef)
          val t1 = System.currentTimeMillis()
          val infRes = solver()
          val funcTime = (System.currentTimeMillis() - t1) / 1000.0
          infRes match {
            case Some(InferResult(true, model, inferredFuns)) =>
              val funsWithTemplates = inferredFuns.filter { fd =>
                val origFd = Util.functionByName(fd.id.name, ctx.program).get
                !analyzedSet.contains(origFd) && origFd.hasTemplate
              }
              // create a inference condition for reporting
              var first = true
              funsWithTemplates.foreach { fd =>
                val origFd = Util.functionByName(fd.id.name, ctx.program).get
                val inv = TemplateInstantiator.getAllInvariants(model.get,
                  Map(origFd -> origFd.getTemplate))
                // record the inferred invariants
                val ic = new InferenceCondition(Some(inv(origFd)), fd)
                ic.time = if (first) Some(funcTime) else Some(0.0)
                // update analyzed set
                analyzedSet += (origFd -> ic)
                first = false
              }
              val invs = TemplateInstantiator.getAllInvariants(model.get,
                funsWithTemplates.collect {
                  case fd if fd.hasTemplate => fd -> fd.getTemplate
                }.toMap)
              if (ctx.modularlyAnalyze) {
                // create a new program that has the inferred templates
                val funToTmpl = prog.definedFunctions.collect {
                  case fd if !invs.contains(fd) && fd.hasTemplate =>
                    fd -> fd.getTemplate
                }.toMap
                assignTemplateAndCojoinPost(funToTmpl, prog, invs)
              } else
                prog
            case _ =>
              reporter.info("- Exhausted all templates, cannot infer invariants")
              val ic = new InferenceCondition(None, origFun)
              ic.time = Some(funcTime)
              analyzedSet += (origFun -> ic)
              prog
          }
        } else {
          //nothing needs to be done here
          reporter.info("Function does not have a body or postcondition")
          prog
        }
      } else prog
    }
    analyzedSet
  }
}
