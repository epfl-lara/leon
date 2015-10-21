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
import transformations._
import leon.utils._
import Util._
import PredicateUtil._
import ProgramUtil._
import SolverUtil._

/**
 * @author ravi
 * This phase performs automatic invariant inference.
 * TODO: should time be implicitly made positive
 */
class InferenceEngine(ctx: InferenceContext) extends Interruptible {

  val ti = new TimeoutFor(this)

  def interrupt() = {
    ctx.abort = true
    ctx.leonContext.interruptManager.interrupt()
  }

  def recoverInterrupt() = {
    ctx.abort = false
  }

  def runWithTimeout() = {
    ctx.totalTimeout match {
      case Some(t) => // timeout in secs
        ti.interruptAfter(t * 1000) {
          run
        }
      case None =>
        run
    }
  }

  private def run(): InferenceReport = {
    val reporter = ctx.reporter
    val program = ctx.inferProgram
    reporter.info("Running Inference Engine...")

    //register a shutdownhook
    if (ctx.dumpStats) {
      sys.ShutdownHookThread({ dumpStats(ctx.statsSuffix) })
    }
    val t1 = System.currentTimeMillis()
    //compute functions to analyze by sorting based on topological order (this is an ascending topological order)
    val callgraph = CallGraphUtil.constructCallGraph(program, withTemplates = true)
    val functionsToAnalyze = ctx.functionsToInfer match {
      case Some(rootfuns) =>
        val rootset = rootfuns.toSet
        val rootfds = program.definedFunctions.filter(fd => rootset(InstUtil.userFunctionName(fd)))
        val relfuns = rootfds.flatMap(callgraph.transitiveCallees _).toSet
        callgraph.topologicalOrder.filter { fd => relfuns(fd) }
      case _ =>
        callgraph.topologicalOrder
    }
    //reporter.info("Analysis Order: " + functionsToAnalyze.map(_.id))
    var results: Map[FunDef, InferenceCondition] = null
    if (!ctx.useCegis) {
      results = analyseProgram(program, functionsToAnalyze)
      //println("Inferrence did not succeeded for functions: "+functionsToAnalyze.filterNot(succeededFuncs.contains _).map(_.id))
    } else {
      var remFuncs = functionsToAnalyze
      var b = 200
      var maxCegisBound = 200
      breakable {
        while (b <= maxCegisBound) {
          Stats.updateCumStats(1, "CegisBoundsTried")
          val succeededFuncs = analyseProgram(program, remFuncs)
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
    new InferenceReport(results.map(pair => {
      val (fd, ic) = pair
      (fd -> List[VC](ic))
    }), program)(ctx)
  }

  def dumpStats(statsSuffix: String) = {
    //pick the module id.
    val modid = ctx.inferProgram.modules.last.id
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
  def analyseProgram(startProg: Program, functionsToAnalyze: Seq[FunDef]): Map[FunDef, InferenceCondition] = {
    val reporter = ctx.reporter
    val funToTmpl =
      if (ctx.autoInference) {
        //A template generator that generates templates for the functions (here we are generating templates by enumeration)
        // not usef for now
        /*val tempFactory = new TemplateFactory(Some(new TemplateEnumerator(ctx, startProg)),
            startProg, ctx.reporter)*/
        startProg.definedFunctions.map(fd => fd -> getOrCreateTemplateForFun(fd)).toMap
      } else
        startProg.definedFunctions.collect { case fd if fd.hasTemplate => fd -> fd.getTemplate }.toMap
    val progWithTemplates = assignTemplateAndCojoinPost(funToTmpl, startProg)
    var analyzedSet = Map[FunDef, InferenceCondition]()

    functionsToAnalyze.filterNot((fd) => {
      (fd.annotations contains "verified") ||
        (fd.annotations contains "library") ||
        (fd.annotations contains "theoryop")
    }).foldLeft(progWithTemplates) { (prog, origFun) =>

      if (ctx.abort) {
        reporter.info("- Aborting analysis of " + origFun.id.name)
        val ic = new InferenceCondition(Seq(), origFun)
        ic.time = Some(0)
        prog
      } else if (origFun.getPostWoTemplate == tru && !origFun.hasTemplate) {
        reporter.info("- Nothing to solve for " + origFun.id.name)
        prog
      } else {
        val funDef = functionByName(origFun.id.name, prog).get
        reporter.info("- considering function " + funDef.id.name + "...")
        //skip the function if it has been analyzed
        if (!analyzedSet.contains(origFun)) {
          if (funDef.hasBody && funDef.hasPostcondition) {
            // for stats
            Stats.updateCounter(1, "procs")
            val solver =
              if (funDef.annotations.contains("compose")) //compositional inference ?
                new CompositionalTimeBoundSolver(ctx, prog, funDef)
              else
                new UnfoldingTemplateSolver(ctx, prog, funDef)
            val t1 = System.currentTimeMillis()
            val infRes = solver()
            val funcTime = (System.currentTimeMillis() - t1) / 1000.0
            infRes match {
              case Some(InferResult(true, model, inferredFuns)) =>
                // create a inference condition for reporting
                var first = true
                inferredFuns.foreach { fd =>
                  val origFd = functionByName(fd.id.name, startProg).get
                  val inv = if (origFd.hasTemplate) {
                    TemplateInstantiator.getAllInvariants(model.get,
                      Map(origFd -> origFd.getTemplate))(origFd)
                  } else {
                    val currentInv = TemplateInstantiator.getAllInvariants(model.get,
                      Map(fd -> fd.getTemplate))(fd)
                    // map result variable  in currentInv
                    val repInv = replace(Map(getResId(fd).get.toVariable -> getResId(origFd).get.toVariable), currentInv)
                    translateExprToProgram(repInv, prog, startProg)
                  }
                  // record the inferred invariants
                  if (analyzedSet.contains(origFd)) {
                    val ic = analyzedSet(origFd)
                    ic.addInv(Seq(inv))
                  } else {
                    val ic = new InferenceCondition(Seq(inv), origFd)
                    ic.time = if (first) Some(funcTime) else Some(0.0)
                    // update analyzed set
                    analyzedSet += (origFd -> ic)
                    first = false
                  }
                }
                val funsWithTemplates = inferredFuns.filter { fd =>
                  val origFd = functionByName(fd.id.name, startProg).get
                  !analyzedSet.contains(origFd) && origFd.hasTemplate
                }
                val invs = TemplateInstantiator.getAllInvariants(model.get,
                  funsWithTemplates.collect {
                    case fd if fd.hasTemplate => fd -> fd.getTemplate
                  }.toMap)
                // create a new program that has the inferred templates
                val funToTmpl = prog.definedFunctions.collect {
                  case fd if !invs.contains(fd) && fd.hasTemplate =>
                    fd -> fd.getTemplate
                }.toMap
                assignTemplateAndCojoinPost(funToTmpl, prog, invs)

              case _ =>
                reporter.info("- Exhausted all templates, cannot infer invariants")
                val ic = new InferenceCondition(Seq(), origFun)
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
    }
    analyzedSet
  }
}
