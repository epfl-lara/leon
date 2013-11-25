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
import leon.verification.ExtendedVC
import leon.verification.Tactic
import leon.verification.VerificationReport
import leon.invariant._
import scala.collection.mutable.{Set => MutableSet}
import leon.purescala.ScalaPrinter
import leon.solvers.SimpleSolverAPI
import leon.solvers.SolverFactory
import leon.solvers.z3.UIFZ3Solver
import leon.verification.VerificationReport

/**
 * @author ravi
 * This phase performs automatic invariant inference. 
 * TODO: Fix the handling of getting a template for a function, the current code is very obscure
 */
object InferInvariantsPhase extends LeonPhase[Program, VerificationReport] {
  val name = "InferInv"
  val description = "Invariant Inference"
  val fls = BooleanLiteral(false)
  
  //control printing of statisticcs
  val dumpStats = false
  
  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("monotones", "--monotones=f1:f2", "Monotonic functions f1,f2,..."),
    LeonValueOptionDef("modularize", "--modularize=f1:f2", "Perform modular analysis on f1,f2,..."),
    LeonValueOptionDef("timeout", "--timeout=T", "Timeout after T seconds when trying to prove a verification condition."),
    LeonValueOptionDef("enumrel", "--enumrel=T", "The realtion that would be used for enumeration"))

  //TODO: handle direct equality and inequality on ADTs
  //TODO: Do we need to also assert that time is >= 0
  class InferenceEngineGenerator(reporter: Reporter, program: Program, context: LeonContext) {

    def getInferenceEngine(funDef: FunDef, tempFactory : TemplateFactory)
    	: (() => (Option[Boolean],Option[Expr])) = {

      //Create and initialize a constraint tracker
      val constTracker = new ConstraintTracker(funDef)
      
      //create a body and post of the function
      val body = funDef.body.get
      val (resid,post) = funDef.postcondition.get
      val resvar = resid.toVariable
      
      //val resFresh = Variable(FreshIdentifier("result", true).setType(body.getType))      
      val simpBody = matchToIfThenElse(body)
      val plainBody = Equals(resvar, simpBody)      
      val bodyExpr = if (funDef.hasPrecondition) {        
        And(matchToIfThenElse(funDef.precondition.get), plainBody)
      } else plainBody 
      val postExpr = matchToIfThenElse(post) 
      val npost = ExpressionTransformer.normalizeExpr(Not(postExpr))
      
      //flatten the functions in the body           
      val flatBody = ExpressionTransformer.normalizeExpr(bodyExpr)
      //for debugging
      println("falttened Body: " + flatBody)      
      constTracker.addBodyConstraints(funDef, flatBody)      
      
      //create a postcondition template if the function is recursive or if a template is provided for the function      
      val npostTemp = if (program.isRecursive(funDef) || FunctionInfoFactory.hasTemplate(funDef)) {
        
        //this is a way to create an idenitity map :-))
        val argmap = InvariantUtil.formalToAcutal(Call(resvar, FunctionInvocation(funDef, funDef.args.map(_.toVariable))))
          
        val temp = tempFactory.constructTemplate(argmap, funDef)
        Some(ExpressionTransformer.normalizeExpr(Not(temp)))
      } else None

      //add the negation of the post-condition "or" the template
      //note that we need to use Or as we are using the negation of the disjunction
      val fullPost = if (npostTemp.isDefined) {
        if (npost == fls) npostTemp.get
        else Or(npost, npostTemp.get)
      } else npost
      
      if(fullPost == fls){
        throw new IllegalStateException("post is true, nothing to be proven!!")        
      }
      
      //for debugging
      println("Flattened Post: "+fullPost)      
      constTracker.addPostConstraints(funDef, fullPost)      

      //create entities that uses the constraint tracker
      val lsAnalyzer = new LinearSystemAnalyzer(constTracker,  tempFactory, context, program, timeout)
      val vcRefiner = new RefinementEngine(program, constTracker, tempFactory, reporter)
      vcRefiner.initialize()

      var refinementStep: Int = 0
      val inferenceEngine = () => {

        val refined =
          if (refinementStep >= 1) {

            reporter.info("- More unrollings for invariant inference")

            val unrolledCalls = vcRefiner.refineAbstraction()
            if (unrolledCalls.isEmpty) {
              reporter.info("- Cannot do more unrollings, reached unroll bound")
              false
            }
            else true            
          } else true

        refinementStep += 1

        if (!refined) (Some(false),None)
        else {
          //solve for the templates in this unroll step          
          val res = lsAnalyzer.solveForTemplatesIncr()

          if (res.isDefined) {

            var output = "Invariants for Function: "+funDef.id+"\n"
            res.get.foreach((pair) => {
              val (fd, inv) = pair
              reporter.info("- Found inductive invariant: " + fd.id + " --> " + inv)
              output += fd.id + " --> " + inv + "\n"
            })
            //add invariants to stats
            Stats.addOutput(output)
            
            reporter.info("- Verifying Invariants... ")

            val verifierRes = verifyInvariant(program, context, reporter, res.get, funDef)
            //val verifierRes = (Some(false),Map())
            verifierRes._1 match {
              case Some(false) => {
                reporter.info("- Invariant verified")
                //return the invariant for the root function
                (Some(true),Some(if(res.get.contains(funDef)) res.get(funDef) else BooleanLiteral(true)))                
              }
              case Some(true) => {
                reporter.error("- Invalid invariant, model: " + verifierRes._2)
                throw IllegalStateException("")              
              }
              case _ => {
                //the solver timed out here
                reporter.error("- Unable to prove or disprove invariant, the invariant is probably true")
                //return the invariant for the root function
                (Some(true),Some(res.get(funDef)))
              }
            }            
          } else {            
            //here, we do not know if the template is solvable or not, we need to do more unrollings.
            (None,None)
          }
        }
      }
      inferenceEngine
    }
  }
  
  /**
   * This function creates a new program with each functions postcondition strengthened by
   * the inferred postcondition
   */
  def verifyInvariant(program: Program, ctx: LeonContext, reporter: Reporter,
    newposts: Map[FunDef, Expr], rootfd: FunDef): (Option[Boolean], Map[Identifier,Expr]) = {

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
        if (fd.postcondition.isDefined){
          val (resvar,postExpr) = fd.postcondition.get 
          Some((resvar,And(postExpr, inv)))
        }          
        else {
          //replace #res in the invariant by a new result variable
          val resvar = FreshIdentifier("res", true).setType(fd.returnType)
          val ninv = replace(Map(ResultVariable() -> resvar.toVariable),inv)
          Some((resvar,ninv))
        }
      } else fd.postcondition

      newfd.postcondition = if (newpost.isDefined) {
        val (resvar, pexpr) = newpost.get
        Some(resvar, searchAndReplaceDFS(replaceFun)(pexpr))
      } else None
    })

    val newDefs = program.mainObject.defs.map {
      case fd: FunDef => newFundefs(fd)
      case d => d
    }

    val newprog = program.copy(mainObject = program.mainObject.copy(defs = newDefs))
    //println("Program: "+newprog)
    //println(ScalaPrinter(newprog))

    val defaultTactic = new DefaultTactic(reporter)
    defaultTactic.setProgram(newprog)
    val vc = defaultTactic.generatePostconditions(newFundefs(rootfd))(0)

    val verifyTimeout = 5
    val fairZ3 = new SimpleSolverAPI(
        new TimeoutSolverFactory(SolverFactory(() => new FairZ3Solver(ctx, newprog)), 
        verifyTimeout * 1000))       
    //println("Func : "+ vc.funDef + " new vc: "+vc.condition)            
    val sat = fairZ3.solveSAT(Not(vc.condition))    
//    if(sat._1 == Some(true)){
//      val evaluator = new DefaultEvaluator(ctx, newprog)
//      
//      simplePostTransform((e: Expr) => e match {
//        case FunctionInvocation(_,_) => {
//          println(e + " --> "+evaluator.eval(e, sat._2))
//          e
//        }
//        case _ => e
//      })(vc.condition)      
//    }
    sat
  }
  

  //TODO provide options
  var timeout: Int = 10  //default timeout is 10s
  var enumerationRelation : (Expr,Expr) => Expr = LessEquals
  def run(ctx: LeonContext)(program: Program): VerificationReport = {

    val reporter = ctx.reporter                 
    reporter.info("Running Invariant Inference Phase...")

    var modularFunctions = Set[FunDef]()
    //val functionsToAnalyse: MutableSet[String] = MutableSet.empty    

    for (opt <- ctx.options) opt match {
//      case LeonValueOption("functions", ListValue(fs)) =>
//        functionsToAnalyse ++= fs

      case LeonValueOption("monotones", ListValue(fs)) => {
        val names = fs.toSet
        program.definedFunctions.foreach((fd) =>{
          //here, checking for name equality without identifiers
          if(names.contains(fd.id.name)) {
            FunctionInfoFactory.setMonotonicity(fd)
            println("Marking "+fd.id+" as monotonic")
          }
        })
      } 
      
      case LeonValueOption("modularize", ListValue(fs)) => {
        val names = fs.toSet
        program.definedFunctions.foreach((fd) =>{
          //here, checking for name equality without identifiers
          if(names.contains(fd.id.name)) {
            modularFunctions += fd
            println("Marking "+fd.id+" as modular")
          }
        })
      }
      
      case v @ LeonValueOption("enumrel", ListValue(ops)) => {        
        val op = ops(0)
        if(op.equals("equals")) enumerationRelation = Equals.apply _
        else if(op.equals("lessequals")) enumerationRelation = LessEquals
        else throw IllegalStateException("Unknown Enumeration Operation")        
      }
        
      case v @ LeonValueOption("timeout", _) =>
        timeout = v.asInt(ctx).get

      case _ =>
    }

    val t1 = System.currentTimeMillis()
    
    //this is an inference engine that checks if there exists an invariant belonging to the current templates 
    val infEngineGen = new InferenceEngineGenerator(reporter, program, ctx)
    //A template generator that generates templates for the functions (here we are generating templates by enumeration)          
    val tempFactory = new TemplateFactory(Some(new TemplateEnumerator(program, reporter, enumerationRelation)), reporter)
    
    //compute functions to analyze by sorting based on topological order
    val callgraph = CallGraphUtil.constructCallGraph(program, withTemplates=true)
    
    //sorting functions in topological order
    def insert(index : Int, l : Seq[FunDef], fd: FunDef) : Seq[FunDef] ={
      var i = 0
      var head = Seq[FunDef]()      
      l.foreach((elem) => {
        if(i == index)
          head :+= fd
        head :+= elem
        i += 1
      })
      head
    }
    var funcList = Seq[FunDef]()
    program.definedFunctions.toList.foreach((f) =>{
      var inserted = false
      var index = 0
      for(i <- 0 to funcList.length - 1) {
        if(!inserted && callgraph.transitivelyCalls(funcList(i),f)) {
          index = i
          inserted = true 
        }        
      }
      if(!inserted) 
        funcList :+= f
        else funcList = insert(index, funcList, f)
    })
    
    val functionsToAnalyze = funcList      
    reporter.info("Analysis Order: "+functionsToAnalyze.map(_.id))
    
    val analysedFunctions: MutableSet[String] = MutableSet.empty
    functionsToAnalyze.foreach((funDef) => {
      analysedFunctions += funDef.id.name      

      if (funDef.body.isDefined && funDef.postcondition.isDefined) {
        val body = funDef.body.get
        val (resvar,post) = funDef.postcondition.get                

        reporter.info("- considering function " + funDef.id + "...")
        reporter.info("Body: " + simplifyLets(body))
        reporter.info("Post: " + simplifyLets(post))

        /*if (post == BooleanLiteral(true)) {
          reporter.info("Post is true, nothing to be proven!!")
        } else {*/                             

        var solved: Option[Boolean] = None
        while (!solved.isDefined) {

          val infEngine = infEngineGen.getInferenceEngine(funDef, tempFactory)
          var infRes: (Option[Boolean],Option[Expr]) = (None, None)         

          //each call to infEngine performs unrolling of user-defined procedures in templates
          while (!infRes._1.isDefined) {
            infRes = infEngine()
          }
          solved = infRes._1 match {
            case Some(true) => {
              //here, if modularize flag is set for the function then update the templates with the inferred invariant
              if(modularFunctions.contains(funDef)) {
                tempFactory.setTemplate(funDef, infRes._2.get)            
              }
              Some(true)
            }
            case Some(false) => {
              reporter.info("- Template not solvable!!")
              //refine the templates here
              val refined = tempFactory.refineTemplates()
              if (refined) None
              else Some(false)
            }
            case _ => throw new IllegalStateException("This case is not possible")
          }
        }
        if (!solved.get) {
          reporter.info("- Exhausted all templates, cannot infer invariants")
          System.exit(0)
        }              
      }
    })
    val t2 = System.currentTimeMillis()
    Stats.totalTime = t2 - t1
    //dump stats 
    if (dumpStats) {
      reporter.info("- Dumping statistics")
      Stats.dumpStats(new PrintWriter("stats" + FileCountGUID.getID))
    }
    
    VerificationReport.emptyReport
  }
}
