package leon
package invariant

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TrivialSolver, TimeoutSolver }
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
import leon.verification.ExtendedVC
import leon.verification.Tactic
import leon.verification.VerificationReport
import leon.invariant._
import scala.collection.mutable.{Set => MutableSet}

/**
 * @author ravi
 * This phase performs automatic invariant inference. 
 */
object InferInvariantsPhase extends LeonPhase[Program, VerificationReport] {
  val name = "InferInv"
  val description = "Invariant Inference"
  
  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("timeout", "--timeout=T", "Timeout after T seconds when trying to prove a verification condition."))

  class InferenceEngine(reporter: Reporter, program: Program, context: LeonContext,
      vc: ExtendedVC,
      uisolver: UninterpretedZ3Solver) {        
    
    def getInferenceEngine(fundef: FunDef): (() => Boolean) = {
      
      val vcRefiner = new RefinementEngine(vc.condition,vc.funDef,program)      
      val constTracker = new ConstraintTracker(fundef)
      val templateFactory = new TemplateFactory()
      var refinementStep : Int = 0

      /**
      * Initialize refinement engine
      **/
      //find the result variable used in the post-condition
      //TODO: make the result variable unique so as to avoid conflicts           

      //add given post conditions
      constTracker.addPostConstraints(vc.funDef,vc.post)          

      //add post condition template if the function is recursive
      if(program.isRecursive(vc.funDef)) {
      	val resultVar = variablesOf(vc.post).find(_.name.equals("result")).first
      	val baseTerms = vc.funDef.args.map(_.toVariable) :+ Variable(resultVar)          
      	val funcTemps = templateFactory.constructTemplate(baseTerms, vc.funDef)      
      	funcTemps.foreach(constTracker.addTemplatedPostConstraint(vc.funDef,_))
      }

			//add body constraints (body condition templates will be added during solving)
      constTracker.addBodyConstraints(vc.funDef,vc.body)
          
      val inferenceEngine = () => {
        
        if(refinementStep >=0) {
          val unrollSet = vcRefiner.refineAbstraction()
          val (call, recCaller, body, post) = unrollSet

					//compute the formal to the actual argument mapping   
					val funRes = variablesOf(body.get).find(_.name.equals("result")).first       
					val argmap = Map(funRes -> call.retexpr) ++ call.fi.fd.args.zip(call.fi.args)
					
          /**
           * process the unroll set
           * (a) check if the calls are recursive. 
           * (b) If not just inline their body and add it to the tree of the caller
           * (c) If yes create a new tree with the function definitions if one does not exists           			 
           */          					
          if(program.isRecursive(call)) {

						val targetFun = call.fi.funDef
          	//check if a constraint tree does not exist for the call's target          	
          	if(!constTracker.hasTree(targetFun)){          		
          		
							consTracker.addPostConstraints(targetFun, body.get)
							if(post.isDefined) 
          			consTracker.addPostConstraints(targetFun, post.get)          		

							//add post condition template for the function
							val bts = targetFun.args.map(_.toVariable) :+ funRes
          		val posttemps = templateFactory.constructTemplate(bts, targetFun)	
          		posttemps.foreach(constTracker.addTemplatedBodyConstraints(recCaller,_)) 
          	}

          	//get the template for the targetFun and replace formal arguments by
          	//actual arguments in the template and add it to the caller body constraints         
          	//val argterms = fi.args.map(_.toVariable) :+ call.resexpr          
          	//val temps = templateFactory.constructTemplate(argterms, targetFun)	
          	//temps.foreach(constTracker.addTemplatedBodyConstraints(recCaller,_)) 
          }
          else {          
						//replace formal parameters by actual arguments in the body and the post					
						val calleeCond = if(post.isDefined) And(body.get,post.get) else body.get          						
						val newcond = replace(argmap,calleeCond)						

						//add to caller constraints
						constTracker.addBodyConstraints(recCaller, newcond)						          	      
          }                             
        }

        //solve for the templates at this unroll step          
        val templateSynthesizer = templateFactory.getTemplateSynthesizer()
        val res = constTracker.solveForTemplates(templateSynthesizer, uisolver)
        
        if (res.isDefined) {                       
        	//TODO to be changed current left unthouched for testing.
          val inv = res.get(vc.funDef)            
          reporter.info("- Found inductive invariant: " + inv)
          //check if this is an invariant 
          reporter.info("- Verifying Invariant " + res.get(fundef))

          //create a new post-condition            
          val newPost = replace(Map(Variable(resultVar) -> ResultVariable()), inv)            			  
          val postExpr = And(fundef.postcondition.get, newPost)
          verifyInvariant(fundef,context,program,postExpr,reporter)
          System.exit(0)
          true
        }
        else false           

       refinementStep += 1
      }
      inferenceEngine     
    }
  }
  
  /**
   * create a program with the input function replaced by a new function that has the new postcondition
   */
  def verifyInvariant(fundef: FunDef, ctx: LeonContext, program: Program, newpost: Expr, reporter: Reporter): Boolean = {
    
    val newfundef = new FunDef(FreshIdentifier(fundef.id.name, true), fundef.returnType, fundef.args)
    //replace the recursive invocations by invocations of the new function  
    val newbody = searchAndReplaceDFS((e: Expr) => (e match {
      case fi @ FunctionInvocation(fd, args) if (fd == fundef) => Some(FunctionInvocation(newfundef, args))
      case _ => None
    }))(fundef.body.get)
    newfundef.body = Some(newbody)
    //assuming pre and postconditions do not have recursive calls
    //TODO: Noncritical correctness issue: fix this                    
    newfundef.precondition = fundef.precondition
    newfundef.postcondition = Some(newpost)
    val newfuncs = program.mainObject.definedFunctions.filter(_ != fundef) :+ newfundef
    val newObjDef = ObjectDef(program.mainObject.id.freshen, newfuncs ++ program.mainObject.definedClasses, program.mainObject.invariants)
    val newprog = Program(program.id.freshen, newObjDef)
    //println("Program: "+newprog)

    val defaultTactic = new DefaultTactic(reporter)
    defaultTactic.setProgram(newprog)
    val vc = defaultTactic.generatePostconditions(newfundef).first

    val fairZ3 = new FairZ3Solver(ctx)
    fairZ3.setProgram(newprog)
    //println("Func : "+ vc.funDef + " new vc: "+vc.condition)            
    val sat = fairZ3.solveSAT(Not(vc.condition))
    sat._1 match {
      case Some(false) => {
        reporter.info("- Invariant verified")
        true
      }
      case Some(true) => {
        reporter.error("- Invalid invariant, model: " + sat._2)        
        System.exit(-1)
        false
      }
      case _ => {
        reporter.error("- Unable to prove or disprove invariant")
        System.exit(-1)
        false
      }
    }
  }  
      
  def run(ctx: LeonContext)(program: Program): VerificationReport = {

    val functionsToAnalyse: MutableSet[String] = MutableSet.empty
    var timeout: Option[Int] = None

    for (opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        functionsToAnalyse ++= fs

      case v @ LeonValueOption("timeout", _) =>
        timeout = v.asInt(ctx)

      case _ =>
    }

    //create an ui solver
    val uisolver = new UninterpretedZ3Solver(ctx)
    uisolver.setProgram(program)    
    val reporter = ctx.reporter
    
    //create a clause listener factory
    val infEngine = new InferenceEngine(reporter,program,ctx,uisolver)

    val trivialSolver = new TrivialSolver(ctx)
    val fairZ3 = new FairZ3Solver(ctx)

    val solvers0: Seq[Solver] = trivialSolver :: fairZ3 :: Nil
    val solvers: Seq[Solver] = timeout match {
      case Some(t) => solvers0.map(s => new TimeoutSolver(s, 1000L * t))
      case None => solvers0
    }

    solvers.foreach(_.setProgram(program))

    val defaultTactic = new DefaultTactic(reporter)
    defaultTactic.setProgram(program)
    /*val inductionTactic = new InductionTactic(reporter)
    inductionTactic.setProgram(program)*/

    def generateVerificationConditions: List[ExtendedVC] = {
      var allVCs: Seq[ExtendedVC] = Seq.empty
      val analysedFunctions: MutableSet[String] = MutableSet.empty

      for (funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2) 
          if (functionsToAnalyse.isEmpty || functionsToAnalyse.contains(funDef.id.name))) {
        analysedFunctions += funDef.id.name

        val tactic: Tactic = defaultTactic

        //add the template as a post-condition to all the methods

        /*allVCs ++= tactic.generatePreconditions(funDef)
          allVCs ++= tactic.generatePatternMatchingExhaustivenessChecks(funDef)*/
        allVCs ++= tactic.generateExtendedVCs(funDef)
        /*allVCs ++= tactic.generateMiscCorrectnessConditions(funDef)
          allVCs ++= tactic.generateArrayAccessChecks(funDef)*/

        allVCs = allVCs.sortWith((vc1, vc2) => {
          val id1 = vc1.funDef.id.name
          val id2 = vc2.funDef.id.name
          if (id1 != id2) id1 < id2 else vc1 < vc2
        })
      }

      val notFound = functionsToAnalyse -- analysedFunctions
      notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

      allVCs.toList
    }

    def checkVerificationConditions(vcs: Seq[ExtendedVC]): VerificationReport = {

      for (vcInfo <- vcs) {
        val funDef = vcInfo.funDef
        /*val body = TransformNot(vcInfo.body)
        val post = TransformNot(vcInfo.post)*/
        val body = vcInfo.body
        val post = vcInfo.post

        reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
        reporter.info("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
        reporter.info("Body: " + simplifyLets(body))
        reporter.info("Post: " + simplifyLets(post))

        // try all solvers until one returns a meaningful answer
        var superseeded: Set[String] = Set.empty[String]
        solvers.find(se => {
          reporter.info("Trying with solver: " + se.name)
          if (superseeded(se.name) || superseeded(se.description)) {
            reporter.info("Solver was superseeded. Skipping.")
            false
          } else {
            superseeded = superseeded ++ Set(se.superseeds: _*)

            //set listeners        	  
            //se.SetModelListener(getModelListener(funDef))
            se.SetInferenceEngine(infEngine.getInferenceEngine(funDef))

            val t1 = System.nanoTime
            se.init()
            //invoke the solver with separate body and post-condition
            //val (satResult, counterexample) = se.solveSAT(Not(vc))
            val (satResult, counterexample) = se.solve(body, post)
            val solverResult = satResult.map(!_)

            val t2 = System.nanoTime
            val dt = ((t2 - t1) / 1000000) / 1000.0

            solverResult match {
              case None => false
              case Some(true) => {
                reporter.info("==== VALID ====")

                vcInfo.value = Some(true)
                vcInfo.solvedWith = Some(se)
                vcInfo.time = Some(dt)

                true
              }
              case Some(false) => {
                reporter.error("Found counter-example : ")
                reporter.error(counterexample.toSeq.sortBy(_._1.name).map(p => p._1 + " -> " + p._2).mkString("\n"))
                reporter.error("==== INVALID ====")
                vcInfo.value = Some(false)
                vcInfo.solvedWith = Some(se)
                vcInfo.time = Some(dt)

                true
              }
            }
          }
        }) match {
          case None => {
            reporter.warning("No solver could prove or disprove the verification condition.")
          }
          case _ =>
        }

      }

      val report = new VerificationReport(vcs)
      report
    }

    reporter.info("Running Invariant Inference Phase...")

    val report = if (solvers.size > 1) {
      reporter.info("Running verification condition generation...")
      checkVerificationConditions(generateVerificationConditions)
    } else {
      reporter.warning("No solver specified. Cannot test verification conditions.")
      VerificationReport.emptyReport
    }

    report
  } 
}