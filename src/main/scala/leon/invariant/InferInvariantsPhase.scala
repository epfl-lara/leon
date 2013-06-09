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
      uisolver: UninterpretedZ3Solver) {        
    
    //TODO: critical: handle unrolling of functions in templates
    def getInferenceEngine(vc: ExtendedVC): (() => Boolean) = {
            
      val constTracker = new ConstraintTracker(vc.funDef)
      //val templateFactory = new TemplateFactory()
      var refinementStep : Int = 0
      
      //flatten the functions in the vc
      val vcbody = InvariantUtil.FlattenFunction(vc.body)
      
      //create a postcondition (this is tricky and may have to use templates)      
      val postTemp = if(program.isRecursive(vc.funDef)) {
        //find the result variable used in the post-condition
    	//TODO: make the result variable unique so as to avoid conflicts
      	val resultVar = variablesOf(vc.post).find(_.name.equals("result")).first
      	
      	val argmap = InvariantUtil.formalToAcutal(
      	    Call(resultVar.toVariable,FunctionInvocation(vc.funDef,vc.funDef.args.map(_.toVariable))),      	    
      	    ResultVariable())
      	    
      	Some(TemplateFactory.constructTemplate(argmap, vc.funDef))      	
      } else {
        None
      }               
      val vcnpost = InvariantUtil.FlattenFunction(Not(vc.post))            
      val cond = And(vcbody,vcnpost)
      val vcRefiner = new RefinementEngine(cond,vc.funDef,program)

      /**
      * Initialize refinement engine
      **/                    
      //add the negation of the post-condition "or" the template
      //note that we need to use Or as we are using the negation of the disjunction
      val fullPost = if(postTemp.isDefined) 
    	  					Or(vcnpost, InvariantUtil.FlattenFunction(Not(postTemp.get)))
    	  			  else vcnpost
      constTracker.addPostConstraints(vc.funDef,fullPost)                
      //add body constraints (body condition templates will be added during solving)
      constTracker.addBodyConstraints(vc.funDef,vcbody)
          
      val inferenceEngine = () => {
        
        if(refinementStep >=1) {
          
          reporter.info("More unrollings for invariant inference")
          //System.exit(0)
          val unrollSet = vcRefiner.refineAbstraction()          
          unrollSet.foreach((entry) => {
            val (call, recCaller, body, post) = entry            
            val targetFun = call.fi.funDef
            
            /**
             * process the unroll set
             * (a) check if the calls are recursive.
             * (b) If not just inline their body and add it to the tree of the caller
             * (c) If yes create a new tree with the function definitions if one does not exists
             */            
            if (program.isRecursive(targetFun)) {              
              //check if a constraint tree does not exist for the call's target          	
              if (!constTracker.hasCtrTree(targetFun)) {

                //add body constraints
                constTracker.addBodyConstraints(targetFun, body.get)

                //add (negated) post condition template for the function                  
                val funRes = variablesOf(body.get).find(_.name.equals("result")).first

                val argmap = InvariantUtil.formalToAcutal(
                  Call(funRes.toVariable, FunctionInvocation(targetFun, targetFun.args.map(_.toVariable))),
                  ResultVariable())

                val postTemp = TemplateFactory.constructTemplate(argmap, targetFun)
                val npostTemp = InvariantUtil.FlattenFunction(Not(postTemp))
                //print the negated post
                //println("Negated Post: "+npostTemp)
                constTracker.addPostConstraints(targetFun,npostTemp)
              }

              //TODO: add the unrolled body to the caller constraints                       
            } else {
              				
              val calleeSummary = if (post.isDefined) And(body.get, post.get) else body.get
              //println("calleeSummary: "+calleeSummary)                                                        
              constTracker.addBodyConstraints(recCaller, calleeSummary)
            }
          })
        }
        refinementStep += 1

        //solve for the templates at this unroll step          
        //val templateSynthesizer = templateFactory.getTemplateSynthesizer()
        val res = constTracker.solveForTemplates(uisolver)

        if (res.isDefined) {

          res.get.foreach((pair) => {
            val (fd, inv) = pair            
            reporter.info("- Found inductive invariant: " + fd.id + " --> " + inv)
          })
          reporter.info("- Verifying Invariants... ")

          verifyInvariant(program, context, reporter, res.get, vc.funDef)
          System.exit(0)
          true
        } else false
      }
      inferenceEngine     
    }
  }

  /**
   * This function creates a new program with each functions postcondition strengthened by
   * the inferred postcondition
   */
  def verifyInvariant(program: Program, ctx: LeonContext, reporter: Reporter,
    newposts: Map[FunDef, Expr], rootfd: FunDef): Boolean = {

    //create a fundef for each function in the program
    val newFundefs = program.mainObject.definedFunctions.map((fd) => {
      val newfd = new FunDef(FreshIdentifier(fd.id.name, true), fd.returnType, fd.args)
      (fd, newfd)
    }).toMap

    val replaceFun = (e: Expr) => e match {
      case fi @ FunctionInvocation(fd1, args) if newFundefs.contains(fd1) =>
        Some(FunctionInvocation(newFundefs(fd1), args))
      case _ => None
    }

    //create a body, pre, post for each newfundef
    newFundefs.foreach((entry) => {
      val (fd, newfd) = entry

      //add a new precondition
      newfd.precondition =
        if (fd.precondition.isDefined)
          Some(searchAndReplaceDFS(replaceFun)(fd.precondition.get))
        else None

      //add a new body
      newfd.body = if (fd.body.isDefined)
        Some(searchAndReplaceDFS(replaceFun)(fd.body.get))
      else None

      //add a new postcondition                  
      val newpost = if (newposts.contains(fd)) {
        val inv = newposts(fd)
        if (fd.postcondition.isDefined)
          Some(And(fd.postcondition.get, inv))
        else Some(inv)
      } else fd.postcondition

      newfd.postcondition = if (newpost.isDefined)
        Some(searchAndReplaceDFS(replaceFun)(newpost.get))
      else None
    })

    val newfuncs = newFundefs.values.toSeq
    val newObjDef = ObjectDef(program.mainObject.id.freshen, newfuncs, program.mainObject.invariants)
    val newprog = Program(program.id.freshen, newObjDef)
    //println("Program: "+newprog)

    val defaultTactic = new DefaultTactic(reporter)
    defaultTactic.setProgram(newprog)
    val vc = defaultTactic.generatePostconditions(newFundefs(rootfd)).first

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
            se.setInferenceEngine(infEngine.getInferenceEngine(vcInfo))

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
