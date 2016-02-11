package leon
package invariant.engine

import purescala._
import purescala.Definitions._
import purescala.ExprOps._
import java.io._
import verification.VC
import scala.util.control.Breaks._
import invariant.factories._
import invariant.util._
import invariant.structure.FunctionUtils._
import transformations._
import leon.utils._
import Util._
import ProgramUtil._
import Stats._

/**
 * @author ravi
 * This phase performs automatic invariant inference.
 * TODO: should time be implicitly made positive
 */
class InferenceEngine(ctx: InferenceContext) extends Interruptible {

  val debugBottomupIterations = false

  val ti = new TimeoutFor(this)

  def interrupt() = {
    ctx.abort = true
    ctx.leonContext.interruptManager.interrupt()
  }

  def recoverInterrupt() = {
    ctx.abort = false
  }

  def runWithTimeout(progressCallback: Option[InferenceCondition => Unit] = None) = {
    ctx.totalTimeout match {
      case Some(t) => // timeout in secs
        ti.interruptAfter(t * 1000) {
          run(progressCallback)
        }
      case None =>
        run(progressCallback)
    }
  }

  private def run(progressCallback: Option[InferenceCondition => Unit] = None): InferenceReport = {
    val reporter = ctx.reporter
    val program = ctx.inferProgram
    reporter.info("Running Inference Engine...")
    if (ctx.dumpStats) { //register a shutdownhook
      sys.ShutdownHookThread({ dumpStats(ctx.statsSuffix) })
    }
    var results: Map[FunDef, InferenceCondition] = null
    time {
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

      if (!ctx.useCegis) {
        results = analyseProgram(program, functionsToAnalyze, defaultVCSolver, progressCallback)
        //println("Inferrence did not succeeded for functions: "+functionsToAnalyze.filterNot(succeededFuncs.contains _).map(_.id))
      } else {
        var remFuncs = functionsToAnalyze
        var b = 200
        val maxCegisBound = 200
        breakable {
          while (b <= maxCegisBound) {
            Stats.updateCumStats(1, "CegisBoundsTried")
            val succeededFuncs = analyseProgram(program, remFuncs, defaultVCSolver, progressCallback)
            remFuncs = remFuncs.filterNot(succeededFuncs.contains _)
            if (remFuncs.isEmpty) break
            b += 5 //increase bounds in steps of 5
          }
          //println("Inferrence did not succeeded for functions: " + remFuncs.map(_.id))
        }
      }
    } { totTime => updateCumTime(totTime, "TotalTime") }
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
    val modid = ctx.inferProgram.modules.find(_.definedFunctions.exists(!_.isLibrary)).get.id
    val filename = modid + statsSuffix + ".txt"
    val pw = new PrintWriter(filename)
    Stats.dumpStats(pw)
    SpecificStats.dumpOutputs(pw)
    if (ctx.tightBounds) {
      SpecificStats.dumpMinimizationStats(pw)
    }
    ctx.reporter.info("Stats dumped to file: "+filename)
  }

  def defaultVCSolver =
    (funDef: FunDef, prog: Program) => {
      if (funDef.annotations.contains("compose")) //compositional inference ?
        new CompositionalTimeBoundSolver(ctx, prog, funDef)
      else
        new UnfoldingTemplateSolver(ctx, prog, funDef)
    }

  /**
   * Returns map from analyzed functions to their inference conditions.
   * TODO: use function names in inference conditions, so that
   * we an get rid of dependence on origFd in many places.
   */
  def analyseProgram(startProg: Program, functionsToAnalyze: Seq[FunDef],
                     vcSolver: (FunDef, Program) => FunctionTemplateSolver,
                     progressCallback: Option[InferenceCondition => Unit]): Map[FunDef, InferenceCondition] = {
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

      if (debugBottomupIterations) {
        println("Current Program: \n",
          ScalaPrinter.apply(prog, purescala.PrinterOptions(printUniqueIds = true)))
        scala.io.StdIn.readLine()
      }

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
            val solver = vcSolver(funDef, prog)
            val (infRes, funcTime) = getTime { solver() }
            infRes match {
              case Some(InferResult(true, model, inferredFuns)) =>
                val origFds = inferredFuns.map { fd =>
                  (fd -> functionByName(fd.id.name, startProg).get)
                }.toMap
                // find functions in the source that had a user-defined template and was solved
                // and it was not previously solved
                val funsWithTemplates = inferredFuns.filter { fd =>
                  val origFd = origFds(fd)
                  !analyzedSet.contains(origFd) && origFd.hasTemplate
                }
                // now the templates of these functions will be replaced by inferred invariants
                val invs = TemplateInstantiator.getAllInvariants(model.get,
                  funsWithTemplates.collect {
                    case fd if fd.hasTemplate => fd -> fd.getTemplate
                  }.toMap)
                // collect templates of remaining functions
                val funToTmpl = prog.definedFunctions.collect {
                  case fd if !invs.contains(fd) && fd.hasTemplate =>
                    fd -> fd.getTemplate
                }.toMap
                val nextProg = assignTemplateAndCojoinPost(funToTmpl, prog, invs)
                // create a inference condition for reporting
                var first = true
                inferredFuns.foreach { fd =>
                  val origFd = origFds(fd)
                  val invOpt = if (funsWithTemplates.contains(fd)) {
                    Some(TemplateInstantiator.getAllInvariants(model.get,
                      Map(origFd -> origFd.getTemplate), prettyInv = true)(origFd))
                  } else if (fd.hasTemplate) {
                    val currentInv = TemplateInstantiator.getAllInvariants(model.get,
                      Map(fd -> fd.getTemplate), prettyInv = true)(fd)
                    // map result variable  in currentInv
                    val repInv = replace(Map(getResId(fd).get.toVariable -> getResId(origFd).get.toVariable), currentInv)
                    Some(translateExprToProgram(repInv, prog, startProg))
                  } else None
                  invOpt match {
                    case Some(inv) =>
                      // record the inferred invariants
                      val inferCond = if (analyzedSet.contains(origFd)) {
                        val ic = analyzedSet(origFd)
                        ic.addInv(Seq(inv))
                        ic
                      } else {
                        val ic = new InferenceCondition(Seq(inv), origFd)
                        ic.time = if (first) Some(funcTime / 1000.0) else Some(0.0)
                        // update analyzed set
                        analyzedSet += (origFd -> ic)
                        first = false
                        ic
                      }
                      progressCallback.foreach(cb => cb(inferCond))
                    case _ =>
                  }
                }
                nextProg

              case _ =>
                reporter.info("- Exhausted all templates, cannot infer invariants")
                val ic = new InferenceCondition(Seq(), origFun)
                ic.time = Some(funcTime / 1000.0)
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
