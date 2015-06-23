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

/**
 * @author ravi
 * This phase performs automatic invariant inference.
 * TODO: Fix the handling of getting a template for a function, the current code is very obscure
 * TODO: should time be implicitly made positive
 */
class InferenceEngine(ctx: InferenceContext) {

  def run(): InferenceReport = {

    val reporter = ctx.reporter
    val program = ctx.program
    reporter.info("Running Invariant Inference Phase...")

    //register a shutdownhook
    if (ctx.dumpStats) {
      sys.ShutdownHookThread({ dumpStats(ctx.statsSuffix) })
    }

    val t1 = System.currentTimeMillis()

    //compute functions to analyze by sorting based on topological order
    val callgraph = CallGraphUtil.constructCallGraph(program, withTemplates = true)

    //sort the functions in topological order (this is an ascending topological order)
    val functionsToAnalyze = if (ctx.modularlyAnalyze) {
      callgraph.topologicalOrder
    } else {
      callgraph.topologicalOrder.reverse
    }

    //reporter.info("Analysis Order: " + functionsToAnalyze.map(_.id))
    var results: Map[FunDef, InferenceCondition] = null
    //perform the invariant inference
    if (!ctx.useCegis) {

      //create a solver factory
      val templateSolverFactory = (constTracker: ConstraintTracker, tempFactory: TemplateFactory, rootFun: FunDef) => {
        if (ctx.withmult) {
          new NLTemplateSolverWithMult(ctx, rootFun, constTracker, tempFactory)
        } else {
          new NLTemplateSolver(ctx, rootFun, constTracker, tempFactory)
        }
      }
      /*val templateSolverFactory = (constTracker: ConstraintTracker, tempFactory: TemplateFactory) => {
        new ParallelTemplateSolver(context, program, constTracker, tempFactory, timeout)
      }*/
      results = analyseProgram(functionsToAnalyze, templateSolverFactory)
      //println("Inferrence did not succeeded for functions: "+functionsToAnalyze.filterNot(succeededFuncs.contains _).map(_.id))
    } else {
      //here iterate on a bound
      var remFuncs = functionsToAnalyze
      //increment cegis bound iteratively
      //var b = 1
      var b = 200
      //var b=1
      var maxCegisBound = 200
      breakable {
        while (b <= maxCegisBound) {

          Stats.updateCumStats(1, "CegisBoundsTried")

          //create a solver factory, ignoring timeouts here
          val templateSolverFactory = (constTracker: ConstraintTracker, tempFactory: TemplateFactory, rootFun: FunDef) => {
            new CegisSolver(ctx, rootFun, constTracker, tempFactory, 10000, Some(b))
            //new CegisSolver(context, program, rootFun, constTracker, tempFactory, 10000, None)
          }
          val succeededFuncs = analyseProgram(remFuncs, templateSolverFactory)
          remFuncs = remFuncs.filterNot(succeededFuncs.contains _)

          if (remFuncs.isEmpty) break;
          //increase bounds in steps of 5
          b += 5
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

  //return a set of functions whose inference succeeded
  def analyseProgram(functionsToAnalyze: Seq[FunDef],
    tempSolverFactory: (ConstraintTracker, TemplateFactory, FunDef) => TemplateSolver): Map[FunDef, InferenceCondition] = {

    val reporter = ctx.reporter
    //this is an inference engine that checks if there exists an invariant belonging to the current templates
    val infEngineGen = new InferenceEngineGenerator(ctx, tempSolverFactory)
    //A template generator that generates templates for the functions (here we are generating templates by enumeration)
    val tempFactory = new TemplateFactory(Some(new TemplateEnumerator(ctx)), ctx.program, ctx.reporter)

    var analyzedSet = Map[FunDef, InferenceCondition]()

    functionsToAnalyze.filterNot((fd) => {
      (fd.annotations contains "verified") ||
        (fd.annotations contains "library") ||
        (fd.annotations contains "theoryop")
    }).foreach((funDef) => {

      reporter.info("- considering function " + funDef.id + "...")
      //skip the function if it has been analyzed
      if (!analyzedSet.contains(funDef)) {
        if (funDef.hasBody && funDef.hasPostcondition) {

          Stats.updateCounter(1, "procs")
          val t1 = System.currentTimeMillis()

          val body = funDef.body.get
          val Lambda(Seq(ValDef(resvar, _)), post) = funDef.postcondition.get          
          // reporter.info("Body: " + simplifyLets(body))
          // reporter.info("Post: " + simplifyLets(post))

          var solved: Option[Boolean] = None
          var infRes: (Option[Boolean], Option[Map[FunDef, Expr]]) = (None, None)
          while (!solved.isDefined) {

            val infEngine = infEngineGen.getInferenceEngine(funDef, tempFactory)
            //each call to infEngine performs unrolling of user-defined procedures in templates
            do {
              infRes = infEngine()
            } while (!infRes._1.isDefined)

            solved = infRes._1 match {
              case Some(true) => {
                Some(true)
              }
              case Some(false) => {
                reporter.info("- Template not solvable!!")
                //refine the templates if necesary
                if (ctx.inferTemp) {
                  val refined = tempFactory.refineTemplates()
                  if (refined) None
                  else Some(false)
                } else Some(false)
              }
              case _ => throw new IllegalStateException("This case is not possible")
            }
          }
          val funcTime = (System.currentTimeMillis() - t1) / 1000.0

          if (solved.get) {
            val inferredFds = (infRes._2.get.keys.toSeq :+ funDef)
            //here, if modularize flag is set then update the templates with the inferred invariant for the analyzed functions
            if (ctx.modularlyAnalyze) {
              infRes._2.get.foreach((pair) => {
                val (fd, inv) = pair
                // note: only user-defined templates are set.
                // Automatically generated ones will be reinferred in each context.
                if (fd.hasTemplate)
                  tempFactory.setTemplate(fd, inv)
              })
            }
            //update some statistics
            var first = 0
            infRes._2.get.foreach(_ match {
              case (fd, inv) => {
                if (!analyzedSet.contains(fd) && fd.hasTemplate) {
                  first += 1
                  val ic = new InferenceCondition(Some(inv), fd)
                  ic.time = if (first == 1) Some(funcTime) else Some(0.0)
                  analyzedSet += (fd -> ic)
                }
              }
            })
          } else {
            reporter.info("- Exhausted all templates, cannot infer invariants")
            val ic = new InferenceCondition(None, funDef)
            ic.time = Some(funcTime)
            analyzedSet += (funDef -> ic)
          }
        } else {
          //nothing needs to be done here
          reporter.info("Function does not have a body or postcondition")
        }
      }
    })
    analyzedSet
  }
}
