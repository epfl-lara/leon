package leon
package verification

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TrivialSolver, TimeoutSolver }
import solvers.z3.FairZ3Solver
//import solvers.princess.PrincessSolver
import scala.collection.mutable.{ Set => MutableSet }
import leon.evaluators._
import java.io._
import scala.tools.nsc.io.File

/**
 * @author ravi
 * This phase performs automatic invariant inference. 
 */
object InferInvariantsPhase extends LeonPhase[Program, VerificationReport] {
  val name = "InferInv"
  val description = "Invariant Inference"
  private var reporter: Reporter = _

  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("timeout", "--timeout=T", "Timeout after T seconds when trying to prove a verification condition."))

  //each constraint is a mapping from constraint variable to its coefficient (integers)
  //a constraint variable can be leon variables or function invocations or case classes etc.
  case class Constraint(val expr: Expr, val coeffMap: Map[Expr, Int], val constant: Set[Int])
  {
    override def toString() : String = {
      "Coeff Map: "+coeffMap+ " Constants: "+constant
    }
  }
  private var goalClauses = Set[Constraint]()

  object ConstraintTreeObject {

    abstract class CtrTree
    case class CtrNode(val blockingId: Identifier, var constraints: Set[Constraint], var children: Set[CtrTree]) extends CtrTree
    {
      override def toString() : String = {
        var str = "Id: "+ blockingId +" Constriants: " + constraints +" children: \n"
        children.foldLeft(str)((g: String,node: CtrTree) => { g + node.toString })        
      }
    }
    case class CtrLeaf() extends CtrTree
    //here we use the name of the id instead of the id itself
    private var treeNodeMap = Map[String, CtrNode]()

    //root of the tree. This would be set while constraints are added
    private var root: CtrTree = CtrLeaf()    

    def addConstraint(e: Expr) = {
      val (id, innerExpr) = parseGuardedExpr(e)
            
      //get the node corresponding to the id
      val ctrnode = treeNodeMap.getOrElse(id.name, {
        val node = CtrNode(id, Set(), Set())
        treeNodeMap += (id.name -> node)        
        node
      })

      innerExpr match {
        case Or(subexprs) => {
          //this should corresponds to a disjunction of literals
          val childIds = subexprs.collect((sube) => sube match {
            case Variable(childId) => childId                                   
            case _ if(sube match{
              //cases to be ignored              
              case Not(Variable(childId)) => false  //need not take this into consideration now
              case _ => true
            }) => throw IllegalStateException("Disjunction has non-variables: " + subexprs)
          })
          for (childId <- childIds)
            createOrAddChildren(ctrnode, childId)
        }
        case Iff(lhs,rhs) =>  {
          val ctr = exprToConstraint(rhs)
          ctrnode.constraints += ctr
        }
        case _ => {
          val ctr = exprToConstraint(innerExpr)
          ctrnode.constraints += ctr
        }
      }
      
      //set the root of the tree (this code is ugly and does string matching)
      //TODO: fix this
      if(id.name.contains("start") && root.isInstanceOf[CtrLeaf]){
         root = ctrnode        
      }
    }

    def createOrAddChildren(parentNode: CtrNode, childId: Identifier) = {
      var childNode = treeNodeMap.getOrElse(childId.name, {
        val node = CtrNode(childId, Set(), Set())
        treeNodeMap += (childId.name -> node)
        node
      })
      parentNode.children += childNode
    }
    
    override def toString() : String = {
      "Constraint Tree: " + root.toString + "\nTreeNodeMapping: "+ treeNodeMap
    }

  }

  def parseGuardedExpr(e: Expr): (Identifier, Expr) = {
    e match {
      case Or(Not(Variable(id)) :: tail) => {
        tail match {
          case expr :: Nil => (id, expr)
          case expr :: tail2 => {
            //this corresponds to a disjunction
            (id, Or(tail))
          }
          case _ => throw IllegalStateException("Not in expected format: " + tail)
        }
      }
      case _ => throw IllegalStateException("Not a guarded expression: " + e)
    }
  }

  //the expr is required to be linear. If not an exception would be thrown
  //for now some of the constructs are not handled
  def exprToConstraint(expr: Expr): Constraint = {
    var coeffMap = Map[Expr, Int]()
    var constant = Set[Int]()

    def recur(e: Expr): Option[Expr] = {
      e match {
        case IntLiteral(v) => {
              constant += v
              None
        }
        case Plus(e1, e2) => {
          if (e1.isInstanceOf[IntLiteral] && e2.isInstanceOf[IntLiteral])
            throw IllegalStateException("sum of two constants, not in canonical form: " + e)

          val r1 = recur(e1)
          if (r1.isDefined) {
            //here the coefficient is 1
            coeffMap += (r1.get -> 1)
          }
          val r2 = recur(e2)
          if (r2.isDefined)
            coeffMap += (r2.get -> 1)

          None
        }
        case Times(e1, e2) => {
          if (e1.isInstanceOf[IntLiteral] && e2.isInstanceOf[IntLiteral])
            throw IllegalStateException("product of two constants, not in canonical form: " + e)

          else if (!e1.isInstanceOf[IntLiteral] && !e2.isInstanceOf[IntLiteral])
            throw IllegalStateException("nonlinear expression: " + e)

          else {
            val (coeff, cvar) = e1 match {
              case IntLiteral(v) => (v, e2)
              case _ => {
                val IntLiteral(v) = e2
                (v, e1)
              }
            }
            val r = recur(cvar)
            if (!r.isDefined)
              throw IllegalStateException("Multiplicand not a constraint variable: " + cvar)
            else {
              //add to mapping
              coeffMap += (r.get -> coeff)
            }
            None
          }
        }
        case Variable(id) => Some(e)
        case FunctionInvocation(fdef, args) => Some(e)
        case BinaryOperator(e1, e2, op) => {
          if (!e.isInstanceOf[Equals] && !e.isInstanceOf[LessThan] && !e.isInstanceOf[LessEquals]
            && !e.isInstanceOf[GreaterThan] && !e.isInstanceOf[GreaterEquals])
            throw IllegalStateException("Relation is not linear: " + e)
          else {
            if (e1.isInstanceOf[IntLiteral] && e2.isInstanceOf[IntLiteral])
              throw IllegalStateException("relation on two integers, not in canonical form: " + e)

            e2 match {
              case IntLiteral(0) => {
                val r = recur(e1)
                if (r.isDefined) {
                  //here the coefficient is 1
                  coeffMap += (r.get -> 1)
                }
                None
              }
              case _ => throw IllegalStateException("Not in canonical form: " + e)
            }
          }
        }
        case _ => {
          throw IllegalStateException("Ecountered unhandled term in the expression: " + e)
        }
      } //end of match e
    } //end of recur      

    val nexpr = MakeLinear(expr)
    if (!recur(nexpr).isDefined) {
      Constraint(nexpr, coeffMap, constant)
    } else
      throw IllegalStateException("Expression not a linear relation: " + nexpr)
  }

  
  /**
   * This method may have to do all sorts of transformation to make the expressions linear constraints
   * This is subjected to constant modification
   */
  def MakeLinear(expr: Expr): Expr = {
    
    //pushes the minus inside the arithmetic terms
    def PushMinus(inExpr : Expr) : Expr = {
      require(inExpr.getType == Int32Type)
      
      inExpr match {
        case IntLiteral(v) => IntLiteral(-v)
        case t : Terminal => Times(IntLiteral(-1),t)
        case fi@FunctionInvocation(fdef,args) => Times(IntLiteral(-1),fi)        
        case UMinus(e1) => e1
        case Minus(e1,e2) => Plus(PushMinus(e1),e2)
        case Plus(e1,e2) => Plus(PushMinus(e1),PushMinus(e2))
        case Times(e1,e2) => {
          //here push the minus in to the coefficient if possible
			e1 match {
              case IntLiteral(v) => Times(PushMinus(e1),e2)
              case _ => Times(e1,PushMinus(e2))
            }          
        }                
        case _ => throw NotImplementedException("PushMinus -- Operators not yet handled: "+inExpr)         
      }
    }
    
    def recur(inExpr: Expr): Expr = {
      inExpr match {        
        case e @ BinaryOperator(e1, e2, op) if (e1.getType == Int32Type &&
            (e.isInstanceOf[Equals] || e.isInstanceOf[LessThan] 
        	|| e.isInstanceOf[LessEquals]|| e.isInstanceOf[GreaterThan] 
        	|| e.isInstanceOf[GreaterEquals])) => {

          e2 match {
            case IntLiteral(0) => e
            case _ => {
              op(recur(Minus(e1, e2)), IntLiteral(0))
            }
          }
        }
        case Minus(e1,e2) => Plus(recur(e1),PushMinus(recur(e2)))
        case UMinus(e1) => PushMinus(recur(e1)) 
        case t : Terminal => t 
        case UnaryOperator(e,op) => op(recur(e))
        case BinaryOperator(e1,e2,op) => op(recur(e1),recur(e2))
        case NAryOperator(args,op) => op(args.map(recur(_))) 
      }
    }
	val nexpr = TransformNot(expr) 
   	recur(nexpr)
  }
  
  
  //TODO: change instance of to match
  def TransformNot(expr: Expr): Expr = {
    def recur(inExpr: Expr): Expr = {
      inExpr match {        
        case Not(e @ BinaryOperator(e1, e2, op)) if (e1.getType == Int32Type)=> {
        	 
			if(e.isInstanceOf[Equals]) {
			  Or(recur(LessEquals(e1,Minus(e2,IntLiteral(1)))),
			      recur(GreaterEquals(e1,Plus(e2,IntLiteral(1)))))
			}              
			else if(e.isInstanceOf[LessThan]) GreaterEquals(recur(e1),recur(e2))			
			else if(e.isInstanceOf[LessEquals]) GreaterThan(recur(e1),recur(e2))
			else if(e.isInstanceOf[GreaterThan]) LessEquals(recur(e1),recur(e2))
			else if(e.isInstanceOf[GreaterEquals]) LessThan(recur(e1),recur(e2))
			else throw IllegalStateException("Unknown integer predicate: "+e)
        }
        case t : Terminal => t 
        case UnaryOperator(e,op) => op(recur(e))
        case BinaryOperator(e1,e2,op) => op(recur(e1),recur(e2))
        case NAryOperator(args,op) => op(args.map(recur(_))) 
      }
    }
    recur(expr)
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

    val reporter = ctx.reporter

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

      for (funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2) if (functionsToAnalyse.isEmpty || functionsToAnalyse.contains(funDef.id.name))) {
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

    def getClauseListener(fundef: FunDef): ((Seq[Expr], Seq[Expr], Seq[Expr]) => Unit) = {
      var counter = 0;
      val listener = (body: Seq[Expr], post: Seq[Expr], newClauses: Seq[Expr]) => {
        //reconstructs the linear constraints corresponding to each path in the programs
        //A tree is used for efficiently representing the set of constraints corresponding to each path

        //initialize the goal clauses
        if (!post.isEmpty) {
          //println("Goal clauses: " + post)          
		  goalClauses ++= post.map((e) => exprToConstraint(parseGuardedExpr(e)._2))
		  println("Goal clauses: "+goalClauses)
        }        
        
        if(!body.isEmpty){
          println("Body clauses: " + body)
          body.map(ConstraintTreeObject.addConstraint(_))
          println(ConstraintTreeObject.toString)          
        }
		System.exit(0)
        
        //initialize the root clauses (corresponds to clauses guarded by the boolean start)

        //add new children to the tree. Each child corresponds to a branch

        /*           for(ncl <- newClauses) { 
                	  println(ncl)
                  }*/
      }
      listener
    }

    def checkVerificationConditions(vcs: Seq[ExtendedVC]): VerificationReport = {

      for (vcInfo <- vcs) {
        val funDef = vcInfo.funDef
        val body = TransformNot(vcInfo.body)
        val post = TransformNot(vcInfo.post)

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
            se.SetClauseListener(getClauseListener(funDef))

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

  /**
   * Dumps an input formula in princess format
   */
  /*var filecount :Int = 0  
  def DumpInPrincessFormat(parts: List[(FunDef,List[Expr])], guard: List[Expr])
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

*/

  /*def getModelListener(funDef: FunDef) : (Map[Identifier, Expr]) => Unit = {
      
      //create an interpolation solver
      val interpolationSolver = new PrincessSolver(ctx)
      val pre = if (funDef.precondition.isEmpty) BooleanLiteral(true) else matchToIfThenElse(funDef.precondition.get)
      val body = matchToIfThenElse(funDef.body.get)
      val resFresh = FreshIdentifier("result", true).setType(body.getType)
      val post = replace(Map(ResultVariable() -> Variable(resFresh)), matchToIfThenElse(funDef.postcondition.get))

      */
  /**
   * This function will be called back by the solver on discovering an input
   */ /*
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
                //println("Final Trace: " + pathcond)

                //convert the guards to princess input
                //DumpInPrincessFormat(parts, pathcond)         
                val interpolants = interpolationSolver.getInterpolants(parts,pathcond)
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
*/

}
