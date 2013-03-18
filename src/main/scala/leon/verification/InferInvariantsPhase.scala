package leon
package verification

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import solvers.{Solver,TrivialSolver,TimeoutSolver}
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{Set => MutableSet}
import leon.evaluators._
import java.io._
import scala.tools.nsc.io.File

/**
 * @author ravi
 * This phase performs automatic invariant inference. For now this simply invokes the leon verifier and 
 * collects symbolic traces using the generated models and computes interpolants
 */
object InferInvariantsPhase extends LeonPhase[Program,VerificationReport] {
  val name = "InferInv"
  val description = "Invariant Inference"    
  private var reporter : Reporter = _ 

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("timeout",   "--timeout=T",       "Timeout after T seconds when trying to prove a verification condition.")
  )

  def run(ctx: LeonContext)(program: Program) : VerificationReport = {
    
    val functionsToAnalyse : MutableSet[String] = MutableSet.empty
    var timeout: Option[Int] = None

    for(opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        functionsToAnalyse ++= fs

      case v @ LeonValueOption("timeout", _) =>
        timeout = v.asInt(ctx)

      case _ =>
    }

    val reporter = ctx.reporter
    val trivialSolver = new TrivialSolver(ctx)    
    val fairZ3 = new FairZ3Solver(ctx)

    val solvers0 : Seq[Solver] = trivialSolver :: fairZ3 :: Nil
    val solvers: Seq[Solver] = timeout match {
      case Some(t) => solvers0.map(s => new TimeoutSolver(s, 1000L * t))
      case None => solvers0
    }

    solvers.foreach(_.setProgram(program))


    val defaultTactic = new DefaultTactic(reporter)
    defaultTactic.setProgram(program)
    /*val inductionTactic = new InductionTactic(reporter)
    inductionTactic.setProgram(program)
*/
    def generateVerificationConditions : List[VerificationCondition] = {
      var allVCs: Seq[VerificationCondition] = Seq.empty
      val analysedFunctions: MutableSet[String] = MutableSet.empty

      for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2) if (functionsToAnalyse.isEmpty || functionsToAnalyse.contains(funDef.id.name))) {
        analysedFunctions += funDef.id.name

        val tactic: Tactic = defaultTactic          

          /*allVCs ++= tactic.generatePreconditions(funDef)
          allVCs ++= tactic.generatePatternMatchingExhaustivenessChecks(funDef)*/
          allVCs ++= tactic.generatePostconditions(funDef)
          /*allVCs ++= tactic.generateMiscCorrectnessConditions(funDef)
          allVCs ++= tactic.generateArrayAccessChecks(funDef)*/
        
        allVCs = allVCs.sortWith((vc1, vc2) => {
          val id1 = vc1.funDef.id.name
          val id2 = vc2.funDef.id.name
          if(id1 != id2) id1 < id2 else vc1 < vc2
        })
      }

      val notFound = functionsToAnalyse -- analysedFunctions
      notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

      allVCs.toList
    }
    
    def getModelListener(funDef: FunDef) : (Map[Identifier, Expr]) => Unit = {

      val pre = if (funDef.precondition.isEmpty) BooleanLiteral(true) else matchToIfThenElse(funDef.precondition.get)
      val body = matchToIfThenElse(funDef.body.get)
      val resFresh = FreshIdentifier("result", true).setType(body.getType)
      val post = replace(Map(ResultVariable() -> Variable(resFresh)), matchToIfThenElse(funDef.postcondition.get))

      /**
       * This function will be called back by the solver on discovering an input
       */
      val processNewInput = (input: Map[Identifier, Expr]) => {
        //create a symbolic trace for pre and body
        var symtraceBody = input.foldLeft(List[Expr]())((g, x) => { g :+ Equals(Variable(x._1), x._2) })
        var parts = List[(FunDef, List[Expr])]()

        //compute the symbolic trace induced by the input
        val (tracePre, partsPre) =
          if (funDef.precondition.isDefined) {
            val resPre = new TraceCollectingEvaluator(ctx, program).eval(pre, input)
            resPre match {
              case EvaluationWithPartitions(BooleanLiteral(true), SymVal(guardPre, valuePre), partsPre) => {
                ((guardPre :+ valuePre), partsPre)
              }
              case _ =>
                reporter.warning("Error in colleting traces for Precondition: " + resPre + " For input: " + input)
                (List[Expr](), List[(FunDef, List[Expr])]())
            }
          } else (List[Expr](), List[(FunDef, List[Expr])]())
        symtraceBody ++= tracePre
        parts ++= partsPre

        //collect traces for body
        val resBody = new TraceCollectingEvaluator(ctx, program).eval(body, input)
        resBody match {
          case EvaluationWithPartitions(cval, SymVal(guardBody, valueBody), partsBody) => {
            //collect traces for the post-condition
            val postInput = input ++ Map(resFresh -> cval)
            val resPost = new TraceCollectingEvaluator(ctx, program).eval(post, postInput)
            resPost match {
              case EvaluationWithPartitions(BooleanLiteral(true), SymVal(guardPost, valuePost), partsPost) => {
                //create a symbolic trace for pre and body
                symtraceBody ++= (guardBody :+ Equals(Variable(resFresh), valueBody))

                //create a set of parts for interpolating
                parts ++= partsBody ++ partsPost :+ (funDef, symtraceBody)

                //print each part for debugging
                //parts.foreach((x) => { println("Method: " + x._1.id + " Trace: " + x._2) })

                //create a symbolic trace including the post condition
                val pathcond = symtraceBody ++ (guardPost :+ valuePost)
                println("Final Trace: " + pathcond)

                //convert the guards to princess input
                ConvertToPrincessFormat(parts, pathcond)
              }
              case EvaluationWithPartitions(BooleanLiteral(true), symval, parts) => {
                reporter.warning("Found counter example for the post-condition: " + postInput)
              }
              case _ => reporter.warning("Error in colleting traces for post: " + resPost + " For input: " + postInput)
            }
          }
          case _ => reporter.warning("Error in colleting traces for body: " + resBody + " For input: " + input)
        }
      }
      
      processNewInput
    }

    def checkVerificationConditions(vcs: Seq[VerificationCondition]) : VerificationReport = {

      for(vcInfo <- vcs) {
        val funDef = vcInfo.funDef
        val vc = vcInfo.condition

        reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
        reporter.info("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
        reporter.info(simplifyLets(vc))

        // try all solvers until one returns a meaningful answer
        var superseeded : Set[String] = Set.empty[String]
        solvers.find(se => {
          reporter.info("Trying with solver: " + se.name)
          if(superseeded(se.name) || superseeded(se.description)) {
            reporter.info("Solver was superseeded. Skipping.")
            false
          } else {
        	  superseeded = superseeded ++ Set(se.superseeds: _*)
        	         		            
        	  //set the model listener
            se.SetModelListener(getModelListener(funDef))

            val t1 = System.nanoTime
            se.init()
            val (satResult, counterexample) = se.solveSAT(Not(vc))
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
    
    val report = if(solvers.size > 1) {
      reporter.info("Running verification condition generation...")
      checkVerificationConditions(generateVerificationConditions)
    } else {
      reporter.warning("No solver specified. Cannot test verification conditions.")
      VerificationReport.emptyReport
    }

    report
  }
  
  var filecount :Int = 0
  
  def ConvertToPrincessFormat(parts: List[(FunDef,List[Expr])], guard: List[Expr])
  {   
	 val file = new java.io.File("princess-output"+filecount+".txt")
	 filecount += 1
	 file.createNewFile()	 
	 val writer = new java.io.BufferedWriter(new java.io.FileWriter(file))
	 
	  //declare the list of free variables (consider only integers for now)
	  val freevars = variablesOf(And(guard))
	  writer.write("\\functions {\n")
	  freevars.foreach((id) => id.getType match {
	    case Int32Type => writer.write("int "+id.toString+";") 
	    case BooleanType => ;//reporter.warning("Boolean types present not handling them for now ")
	    case _ => ;
	  })
	  writer.write("\n}")
	  writer.newLine()
	  
	  //considering only binary operators
	  def appendInfix(lhs: String,rhs: String,op: String) : String = {
	    lhs  + (if(rhs.isEmpty()) "" 
	    	  else if(lhs.isEmpty()) rhs
	    	  else (op +rhs))
	  }
	  
	  //considering only unary operators
	  def appendPrefix(opd: String,op: String) : String = {
	    if(opd.isEmpty()) opd
	    else op + "("+opd+")"
	  }
	  
	  //create a function to convert leon expressions into princess formulas (not all operations are supported)
	  //note: princess does not support boolean type. Hence, we need to replace boolean variables by a predicate
	  // which may introduce disjunctions
	  def PrinForm(formula: Expr) : String = formula match {
	    case And(args) => args.foldLeft(new String())((str,x) => {
	    	appendInfix(str,PrinForm(x)," & ")	    		    	
	    })
	    case Or(args) => args.foldLeft(new String())((str,x) => appendInfix(str,PrinForm(x)," | "))
	    
	    case Variable(id) => id.getType match {
	    							case Int32Type => id.toString	    							
	    							case _ => ""
	    						}
	    case IntLiteral(v) => v.toString
	    case BooleanLiteral(v) => v.toString	    
	    
	    case t@Not(Variable(id)) => reporter.warning("Encountered negation of a variable: " + t); ""
	    case Not(t) => appendPrefix(PrinForm(t),"!")	    
	    case UMinus(t) => appendPrefix(PrinForm(t),"-")
	    	    	   
	    case t@Iff(t1,t2) => {
	     //appendInfix(PrinForm(Implies(t1,t2)),PrinForm(Implies(t2,t1))," & ")
	     //this is a temporary hack to handle the post-condition
	      val (lhs,rhs) = (PrinForm(t1),PrinForm(t2))
	      if(lhs.isEmpty() && rhs.isEmpty()) ""
	      else if(lhs.isEmpty()) PrinForm(t2)
	      else if(rhs.isEmpty()) PrinForm(t1)
	      else {
	       reporter.warning("Both LHS and RHS are bool expressions: "+t);
	       "" 
	      }
	    }
	      					
	    case Implies(t1,t2) => PrinForm(Or(Not(t1),t2))
	    
	    case Equals(t1,t2) => appendInfix(PrinForm(t1),PrinForm(t2),"=")
	    case Plus(t1,t2) => appendInfix(PrinForm(t1),PrinForm(t2),"+")
	    case Minus(t1,t2) => appendInfix(PrinForm(t1),PrinForm(t2),"-")
	    case Times(t1,t2) => appendInfix(PrinForm(t1),PrinForm(t2),"*")
	    case LessThan(t1,t2) => appendInfix(PrinForm(t1),PrinForm(t2),"<")
	    case GreaterThan(t1,t2) => appendInfix(PrinForm(t1),PrinForm(t2),">")
	    case LessEquals(t1,t2) => appendInfix(PrinForm(t1),PrinForm(t2),"<=")
	    case GreaterEquals(t1,t2) => appendInfix(PrinForm(t1),PrinForm(t2),">=")	    
	    case _ => "" //empty string in other cases
	  }
	  
	  //create formula parts
	  writer.write("\\problem{\n")	  
	  
	  var partcount = 0
	  var processedFormulas = List[Expr]()
	  var partnames = List[String]()
	  	  
	  parts.foreach((elem) => {
	    val (func,list) = elem	    
	    
	    val formulas = list -- processedFormulas
	    val partstr = func.id.toString() + partcount
	    writer.write("\\part["+ partstr  +"]"+"\t")
	    writer.write("(" + PrinForm(And(formulas)) +")")
	    
	    if(partcount < parts.length - 1)
	      writer.write(" &\n")
	    else writer.write("\n")
	    
	    //update mutable state variables
	    processedFormulas = processedFormulas ++ formulas
	    partnames = partnames :+ partstr
	    partcount = partcount + 1
	  })
	  
	  //add the implies block
	  writer.write("->\n") 	  
	  
	  //add the final part
	   val leftFormula = guard -- processedFormulas	   
	   writer.write("\\part[assert]"+"\t")
	   writer.write("(" + PrinForm(And(leftFormula)) +")")
	   writer.write("}\n")
	   
	   //add assert to partnames
	   partnames = partnames :+ "assert"
	   
	   //add interpolant blocks	   
	   for( i <- 1 to partnames.length - 1 )  {
	      val (phrase,index) = partnames.foldLeft((new String(),1))(
	      (g,x) => {	      
	    	  	val (ipstr,index) = g
	    	  	if(index == i + 1 && index > 1) (ipstr + ";" + x, index + 1)
	    	  	else if(index > 1) (ipstr + "," + x, index + 1)
	    	  	else (x, index + 1)
	      	})
	      writer.write("\\interpolant {"+phrase+"}\n")	     
	   }
	  writer.flush()
	  writer.close()	  
  }

}
