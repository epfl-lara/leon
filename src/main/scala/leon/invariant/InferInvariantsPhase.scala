package leon
package invariant

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers._
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
import leon.evaluators._
import java.io._
import leon.solvers.z3.UninterpretedZ3Solver
import leon.LeonContext
import leon.LeonOptionDef
import leon.LeonPhase
import leon.LeonValueOption
import leon.ListValue
import leon.Reporter
import leon.verification.DefaultTactic
import leon.verification.Tactic
import leon.verification.VerificationReport
import leon.invariant._
import scala.collection.mutable.{Set => MutableSet}
import leon.purescala.ScalaPrinter
import leon.solvers.SimpleSolverAPI
import leon.solvers.SolverFactory
import leon.solvers.z3.UIFZ3Solver
import leon.verification.VerificationReport
import scala.util.control.Breaks._
import leon.verification.VCKind
import leon.verification.DefaultTactic
import leon.verification.VerificationCondition

/**
 * @author ravi
 * This phase performs automatic invariant inference. 
 * TODO: Fix the handling of getting a template for a function, the current code is very obscure
 * TODO: should time be implicitly made positive
 */
object InferInvariantsPhase extends LeonPhase[Program, VerificationReport] {
  val name = "InferInv"
  val description = "Invariant Inference"
          
  //set by the run method
  var program : Program = null
  var context : LeonContext = null
  var reporter : Reporter = null
  var timeout: Int = 15  //default timeout is 10s
  
  //defualt true flags
  var modularlyAnalyze = true
  var targettedUnroll = true
  
  //default false flags
  var tightBounds = false
  var inferTemp = false
  var enumerationRelation : (Expr,Expr) => Expr = LessEquals  
  var useCegis = false
  //var maxCegisBound = 200 //maximum bound for the constants in cegis
  var maxCegisBound = 1000000000
    
  //control printing of statistics
  val dumpStats = true
  
  override val definedOptions: Set[LeonOptionDef] = Set(
    //LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    //LeonValueOptionDef("monotones", "--monotones=f1:f2", "Monotonic functions f1,f2,..."),
    LeonFlagOptionDef("wholeprogram", "--wholeprogram", "Perform an non-modular whole program analysis"),
    LeonFlagOptionDef("fullunroll", "--fullunroll", "Unroll all calls in every unroll step"),
    LeonFlagOptionDef("minbounds", "--minbounds", "tighten time bounds"),
    LeonValueOptionDef("timeout", "--timeout=T", "Timeout after T seconds when trying to prove a verification condition."),
    LeonFlagOptionDef("inferTemp", "--inferTemp=True/false", "Infer templates by enumeration"),
    LeonFlagOptionDef("cegis", "--cegis=True/false", "use cegis instead of farkas"),
    LeonValueOptionDef("stats-suffix", "--stats-suffix=<suffix string>", "the suffix of the statistics file"))

  //TODO provide options for analyzing only selected functions
  def run(ctx: LeonContext)(prog: Program): VerificationReport = {

    context = ctx
    reporter = ctx.reporter
    program = prog
    reporter.info("Running Invariant Inference Phase...")
    
    var statsSuff = "-stats" + FileCountGUID.getID
    
    //process options
    for (opt <- ctx.options) opt match {
      //      case LeonValueOption("functions", ListValue(fs)) =>
      //        functionsToAnalyse ++= fs

      case LeonFlagOption("wholeprogram", true) => {
        //do not do a modular analysis        
        modularlyAnalyze =false
      }
      
      case LeonFlagOption("fullunroll", true) => {
        //do not do a modular analysis
        targettedUnroll =false
      }
      
      case LeonFlagOption("minbounds", true) => {          
        tightBounds = true
      }

      case v @ LeonFlagOption("inferTemp", true) => {

        inferTemp = true
        var foundStrongest = false
        //go over all post-conditions and pick the strongest relation
        program.definedFunctions.foreach((fd) => {
          if (!foundStrongest && fd.hasPostcondition) {
            val cond = fd.postcondition.get._2
            simplePostTransform((e) => e match {
              case Equals(_, _) => {
                enumerationRelation = Equals.apply _
                foundStrongest = true
                e
              }
              case _ => e
            })(cond)
          }
        })
      }

      case v @ LeonFlagOption("cegis", true) => {        
        useCegis = true
      }

      case v @ LeonValueOption("timeout", _) =>
        timeout = v.asInt(ctx).get

      case v @ LeonValueOption("stats-suffix", ListValue(fs)) => {
        statsSuff = fs(0)
      }
        
      case _ =>
    }
    
    //process annotations
    program.definedFunctions.foreach((fd) => {
      if(fd.annotations.contains("monotonic")){
        val funinfo = FunctionInfoFactory.getOrMakeInfo(fd) 
        funinfo.setMonotonicity        
      }        
    })

    //register a shutdownhook
    if (dumpStats) {
      sys.ShutdownHookThread({ dumpStats(statsSuff) })
    }

    val t1 = System.currentTimeMillis()

    //compute functions to analyze by sorting based on topological order
    val callgraph = CallGraphUtil.constructCallGraph(program, withTemplates = true)

    //sort the functions in topological order (this is an ascending topological order)
    val functionsToAnalyze = if(modularlyAnalyze) {
      callgraph.topologicalOrder      
    } else {
      callgraph.topologicalOrder.reverse
    } 

    reporter.info("Analysis Order: " + functionsToAnalyze.map(_.id))       
    var results : Map[FunDef,InferenceCondition] = null
    //perform the invariant inference
    if(!useCegis) {
      
      //create a solver factory
      val templateSolverFactory = (constTracker: ConstraintTracker, tempFactory: TemplateFactory, rootFun: FunDef) => {
        new NLTemplateSolver(context, program, rootFun, constTracker, tempFactory, timeout, tightBounds)
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
      var maxCegisBound=200
      breakable {
        while (b <= maxCegisBound) {

          Stats.updateCumStats(1, "CegisBoundsTried")
          
          //create a solver factory, ignoring timeouts here                   
          val templateSolverFactory = (constTracker: ConstraintTracker, tempFactory: TemplateFactory, rootFun: FunDef) => {
            new CegisSolver(context, program, rootFun, constTracker, tempFactory, 10000, Some(b))
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
    Stats.updateCumTime(t2-t1, "TotalTime")
    
    //dump stats 
    if (dumpStats) {
      reporter.info("- Dumping statistics")
      dumpStats(statsSuff)
    }
   
    new InferenceReport(results.map(pair => {
      val (fd, ic) = pair
      (fd -> List[VerificationCondition](ic))
    }))
  }
  
  def dumpStats(statsSuffix: String) = {    
    val pw = new PrintWriter(program.mainObject.id + statsSuffix + ".txt")
    Stats.dumpStats(pw)
    SpecificStats.dumpOutputs(pw)
    if (tightBounds) {
      SpecificStats.dumpMinimizationStats(pw)
    }
  }

 
  //return a set of functions whose inference succeeded
  def analyseProgram(functionsToAnalyze : Seq[FunDef], 
      tempSolverFactory : (ConstraintTracker, TemplateFactory, FunDef) => TemplateSolver) : Map[FunDef,InferenceCondition] = {

    //this is an inference engine that checks if there exists an invariant belonging to the current templates 
    val infEngineGen = new InferenceEngineGenerator(program, context, tempSolverFactory, targettedUnroll)
    //A template generator that generates templates for the functions (here we are generating templates by enumeration)          
    val tempFactory = new TemplateFactory(Some(new TemplateEnumerator(program, reporter, enumerationRelation)), reporter)
    
    var analyzedSet = Map[FunDef, InferenceCondition]()

    functionsToAnalyze.filterNot((fd) => {
      val funinfo = FunctionInfoFactory.getFunctionInfo(fd)
      (funinfo.isDefined && funinfo.get.isTheoryOp)
    }).foreach((funDef) => {    

      //skip the function if it has been analyzed
      if (!analyzedSet.contains(funDef)) {        
        if (funDef.hasBody && funDef.hasPostcondition) {
          
          Stats.updateCounter(1, "procs")
          val t1 = System.currentTimeMillis()
          
          val body = funDef.nondetBody.get
          val (resvar, post) = funDef.postcondition.get

          reporter.info("- considering function " + funDef.id + "...")
          reporter.info("Body: " + simplifyLets(body))
          reporter.info("Post: " + simplifyLets(post))

          /*if (post == BooleanLiteral(true)) {
          reporter.info("Post is true, nothing to be proven!!")
        } else {*/

          var solved: Option[Boolean] = None
          var infRes: (Option[Boolean], Option[Map[FunDef,Expr]]) = (None, None)
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
                if (inferTemp) {
                  val refined = tempFactory.refineTemplates()
                  if (refined) None
                  else Some(false)
                } else Some(false)
              }
              case _ => throw new IllegalStateException("This case is not possible")
            }
          }
          val funcTime = (System.currentTimeMillis() - t1)/1000.0
          
          if (solved.get) {
            val inferredFds = (infRes._2.get.keys.toSeq :+ funDef)            
            //here, if modularize flag is set then update the templates with the inferred invariant for the analyzed functions
            if (modularlyAnalyze) {
              infRes._2.get.foreach((pair) => {
                val (fd, inv) = pair
                val funinfo = FunctionInfoFactory.getFunctionInfo(fd)
                if(funinfo.isDefined && funinfo.get.hasTemplate)
                	tempFactory.setTemplate(fd, inv)
              })
            }
            //update some statistics
            var first = 0
            infRes._2.get.foreach(_ match {
              case (fd, inv) => {
                val funinfo = FunctionInfoFactory.getFunctionInfo(fd)
                if (!analyzedSet.contains(fd) && funinfo.isDefined && funinfo.get.hasTemplate) {
                  first += 1
                  val ic = new InferenceCondition(Some(inv), fd)
                  ic.time = if (first == 1) Some(funcTime) else Some(0.0)
                  analyzedSet += (fd -> ic)
                }
              }
            })
          }
          else {
            reporter.info("- Exhausted all templates, cannot infer invariants")
            val ic = new InferenceCondition(None, funDef)
            ic.time = Some(funcTime)
            analyzedSet += (funDef -> ic)
          }
        } else {
          //nothing needs to be done here
        }
      }
    })
    analyzedSet
  }
}
