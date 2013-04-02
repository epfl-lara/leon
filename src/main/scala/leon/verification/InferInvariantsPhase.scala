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
  case class Constraint(val expr: Expr, val coeffMap: Map[Expr, Int], val constant: Option[Int])
  {
    override def toString() : String = {      
      val constStr = coeffMap.foldLeft("")((str,pair) => { 
        val (e,i) = pair
        val termStr = if(i != 1) i + "*" + e.toString 
        			  else e.toString 
        (str + termStr + " + ")        
        }) + 
        (if(constant.isDefined) constant.get.toString
        else "0") +
        (expr match {
          case t : Equals => " = "
          case t : LessThan => " < "
          case t: GreaterThan => " > "
          case t: LessEquals => " <= "
          case t: GreaterEquals => " >= "          
        }) + "0"
        
       constStr //+ " ActualExpr: "+ expr
    }
  }

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
    private var treeNodeMap = Map[Identifier, CtrNode]()

    //root of the tree. This would be set while constraints are added
    var bodyRoot: CtrTree = CtrLeaf()
    var postRoot: CtrTree = CtrLeaf()

    def isBlockingId(id: Identifier): Boolean = {
      if (id.name.startsWith("b")) true else false
    }

    def isStartId(id: Identifier): Boolean = {
      if (id.name.contains("start")) true else false
    }

    ///cleanup this code and do not use flags
    def addConstraint(e: Expr, isBody : Boolean) = {
      val (id, innerExpr) = parseGuardedExpr(e)
            
      //get the node corresponding to the id
      val ctrnode = treeNodeMap.getOrElse(id, {
        val node = CtrNode(id, Set(), Set())
        treeNodeMap += (id -> node)
        
        //set the root of the tree (this code is ugly and does string matching)
      	//TODO: fix this
        if (isStartId(id)) {
          val root = if (isBody) bodyRoot else postRoot
          if (root.isInstanceOf[CtrNode])
            throw IllegalStateException("Different start symbol: " + id)
          else {
            if (isBody) bodyRoot = node else postRoot = node
          }
        }
        
        node
      })

      def addCtrOrBlkLiteral(ie: Expr, newChild : Boolean): Unit = {        
        ie match {
          case Or(subexprs) => {

            val validSubExprs = subexprs.collect((sube) => sube match {
              case _ if (sube match {
                //cases to be ignored              
                case Not(Variable(childId)) => false //need not take this into consideration now
                case _ => true
              }) => sube
            })
            if (!validSubExprs.isEmpty) {              
              val createChild = if (validSubExprs.size > 1) true else false
              for (sube <- validSubExprs) {
                addCtrOrBlkLiteral(sube, createChild)
              }
            }
          }
          //TODO: handle conjunctions as well
          case Variable(childId) => {
            //checking for blocking literal
            if(isBlockingId(childId))
              createOrAddChildren(ctrnode, childId)
              else 
            throw IllegalStateException("Encountered a variable that is not a blocking id: " + childId)
          }             
          case Iff(lhs, rhs) => {
            //lhs corresponds to a blocking id in this case
        	lhs match {
        	  case Variable(childId) if(isBlockingId(childId)) => {
        	     val childNode = createOrAddChildren(ctrnode, childId)
        		 val ctr = exprToConstraint(rhs)
        		 childNode.constraints += ctr
        	  }
        	  case _ => throw IllegalStateException("Iff block --- encountered something that is not a blocking id: " + lhs) 
        	}
            
          }
          case _ => {
            val node = if (newChild) createOrAddChildren(ctrnode, FreshIdentifier("dummy", true))
            			else ctrnode
            val ctr = exprToConstraint(ie)
            node.constraints += ctr
          }                    
        }
      }      
      //important: calling makelinear may result in disjunctions and also potentially conjunctions      
      val nnfExpr = TransformNot(innerExpr)
      addCtrOrBlkLiteral(nnfExpr, false)
    }    

    def createOrAddChildren(parentNode: CtrNode, childId: Identifier) : CtrNode = {
      var childNode = treeNodeMap.getOrElse(childId, {
        val node = CtrNode(childId, Set(), Set())
        treeNodeMap += (childId -> node)
        node
      })
      parentNode.children += childNode
      childNode
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

  //the expr is required to be linear, if not, an exception would be thrown
  //for now some of the constructs are not handled
  def exprToConstraint(expr: Expr): Constraint = {
    var coeffMap = Map[Expr, Int]()
    var constant: Option[Int] = None

    def genConstraint(e: Expr): Option[Expr] = {
      e match {
        case IntLiteral(v) => {
              constant = Some(v)
              None
        }
        case Plus(e1, e2) => {
          if (e1.isInstanceOf[IntLiteral] && e2.isInstanceOf[IntLiteral])
            throw IllegalStateException("sum of two constants, not in canonical form: " + e)

          val r1 = genConstraint(e1)
          if (r1.isDefined) {
            //here the coefficient is 1
            coeffMap += (r1.get -> 1)
          }
          val r2 = genConstraint(e2)
          if (r2.isDefined)
            coeffMap += (r2.get -> 1)

          None
        }
        case Times(e1, e2) => {
          if (e1.isInstanceOf[IntLiteral] && e2.isInstanceOf[IntLiteral])
            throw IllegalStateException("product of two constants, not in canonical form: " + e)

          /*else if (!e1.isInstanceOf[IntLiteral] && !e2.isInstanceOf[IntLiteral])
            throw IllegalStateException("nonlinear expression: " + e)*/
          /*else {
            val (coeff, cvar) = e1 match {
              case IntLiteral(v) => (v, e2)
              case _ => {
                val IntLiteral(v) = e2
                (v, e1)
              }
            }*/
          val IntLiteral(v) = e1
          val (coeff, cvar) = (v, e2)

          val r = genConstraint(cvar)
          if (!r.isDefined)
            throw IllegalStateException("Multiplicand not a constraint variable: " + cvar)
          else {
            //add to mapping
            coeffMap += (r.get -> coeff)
          }
          None          
        }
        case Variable(id) => Some(e)
        case FunctionInvocation(fdef, args) => Some(e)
        case BinaryOperator(e1, e2, op) => {

          /*if (!e.isInstanceOf[Equals] && !e.isInstanceOf[LessThan] && !e.isInstanceOf[LessEquals]
            && !e.isInstanceOf[GreaterThan] && !e.isInstanceOf[GreaterEquals])
            throw IllegalStateException("Relation is not linear: " + e)
          else {*/
          if (e1.isInstanceOf[IntLiteral] && e2.isInstanceOf[IntLiteral])
            throw IllegalStateException("relation on two integers, not in canonical form: " + e)

          e2 match {
            case IntLiteral(0) => {
              val r = genConstraint(e1)
              if (r.isDefined) {
                //here the coefficient is 1
                coeffMap += (r.get -> 1)
              }
              None
            }
            case _ => throw IllegalStateException("Not in canonical form: " + e)
          }
        }
        case _ => {
          throw IllegalStateException("Ecountered unhandled term in the expression: " + e)
        }
      } //end of match e
    } //end of genConstraint      
    
    val linearExpr = MakeLinear(expr)
    if (!genConstraint(linearExpr).isDefined) {
      Constraint(linearExpr, coeffMap, constant)
    } else
      throw IllegalStateException("Expression not a linear relation: " + expr)
  }

  
  /**
   * This method may have to do all sorts of transformation to make the expressions linear constraints.
   * This assumes that the input expression is an atomic predicate (i.e, without and, or and nots)
   * This is subjected to constant modification.
   */
  def MakeLinear(atom: Expr): Expr = {
    
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
    
    //we assume that PushMinus has already been invoked
    def PushTimes(c : Int, ine : Expr) : Expr = {
      require(ine.getType == Int32Type)
      
      ine match {
        case IntLiteral(v) => IntLiteral(c * v)
        case t : Terminal => Times(IntLiteral(c),t)
        case fi@FunctionInvocation(fdef,args) => Times(IntLiteral(c),fi)                       
        case Plus(e1,e2) => Plus(PushTimes(c,e1),PushTimes(c,e2))
        case Times(e1,e2) => {
          //here push the times into the coefficient (which should be the first expression)
        	Times(PushTimes(c,e1),e2)
        }                
        case _ => throw NotImplementedException("PushTimes -- Operators not yet handled: "+ine)         
      }
    }

    //collect all the constants and simplify them
    //we assume that mkLinearRecur has been invoked
    def simplifyConsts(ine: Expr): (Option[Expr], Int) = {
      require(ine.getType == Int32Type)

      ine match {         
        case IntLiteral(v) => (None,v)
        case t: Terminal => (Some(t),0)
        case fi: FunctionInvocation => (Some(fi), 0)       
        case Plus(e1, e2) => {
          val (r1, c1) = simplifyConsts(e1)
          val (r2, c2) = simplifyConsts(e2)

          val newe = (r1, r2) match {
            case (None, None) => None
            case (Some(t), None) => Some(t)
            case (None, Some(t)) => Some(t)
            case (Some(t1), Some(t2)) => Some(Plus(t1, t2))
          }
          (newe, c1 + c2)
        }
        case Times(e1, e2) => {
          //because of the pushTimes assumption, we can simplify this case
          (Some(ine),0)
        }
        case _ => throw NotImplementedException("collectConstants -- Operators not yet handled: "+ine)
      }
    }
   	    
    def mkLinearRecur(inExpr: Expr): Expr = {
      inExpr match {        
        case e @ BinaryOperator(e1, e2, op) if (e1.getType == Int32Type &&
            (e.isInstanceOf[Equals] || e.isInstanceOf[LessThan] 
        	|| e.isInstanceOf[LessEquals]|| e.isInstanceOf[GreaterThan] 
        	|| e.isInstanceOf[GreaterEquals])) => {

          e2 match {
            case IntLiteral(0) => e
            case _ => {
              val r = mkLinearRecur(Minus(e1, e2))
              //simplify the resulting constants
              val (Some(r2),const) = simplifyConsts(r)
              val finale = if(const != 0) Plus(r2,IntLiteral(const)) else r2
              //println(r + " simplifies to "+finale)
              op(finale, IntLiteral(0))
            }
          }
        }
        case Minus(e1,e2) => Plus(mkLinearRecur(e1),PushMinus(mkLinearRecur(e2)))
        case UMinus(e1) => PushMinus(mkLinearRecur(e1))
        case Times(e1,e2) => {
          val (r1,r2) = (mkLinearRecur(e1),mkLinearRecur(e2))
          (r1,r2) match {
            case (IntLiteral(v),_) => PushTimes(v,r2)
            case (_,IntLiteral(v)) => PushTimes(v,r1)
            case _ => throw IllegalStateException("Expression not linear: "+Times(r1,r2))
          }         
        }        
        case Plus(e1,e2) => Plus(mkLinearRecur(e1),mkLinearRecur(e2))
        case t : Terminal => t
        case fi : FunctionInvocation => fi        
        /*case UnaryOperator(e,op) => op(mkLinearRecur(e))
        case BinaryOperator(e1,e2,op) => op(mkLinearRecur(e1),mkLinearRecur(e2))
        case NAryOperator(args,op) => op(args.map(mkLinearRecur(_)))*/
        case _ => throw IllegalStateException("Expression not linear: "+inExpr)
      }
    }	 
   	val rese = mkLinearRecur(atom)
   	//println("Unnormalized Linearized expression: "+unnormLinear)
   	rese
  } 
  
  //TODO: change instanceOf to match
  //It also necessary to convert the formula to negated normal form by pushing all not's inside
  def TransformNot(expr: Expr): Expr = {
    def nnf(inExpr: Expr): Expr = {
      inExpr match {
        //matches integer binary relation
        case Not(e @ BinaryOperator(e1, e2, op)) if (e1.getType == Int32Type) => {
          e match {
            case e: Equals => Or(nnf(LessEquals(e1, Minus(e2, IntLiteral(1)))), nnf(GreaterEquals(e1, Plus(e2, IntLiteral(1)))))
            case e: LessThan => GreaterEquals(nnf(e1), nnf(e2))
            case e: LessEquals => GreaterThan(nnf(e1), nnf(e2))
            case e: GreaterThan => LessEquals(nnf(e1), nnf(e2))
            case e: GreaterEquals => LessThan(nnf(e1), nnf(e2))
            case _ => throw IllegalStateException("Unknown integer predicate: " + e)
          }
        }                
        //TODO: I don't know why "Not" is not recognized as an unary operator
        case e@Not(t: Terminal) => e
        case Not(And(args)) => Or(args.map(arg => nnf(Not(arg))))
        case Not(Or(args)) => And(args.map(arg => nnf(Not(arg))))
        case Not(Not(e1)) => nnf(e1)
        case Not(Implies(e1, e2)) => And(nnf(e1), nnf(Not(e2)))
        case Not(Iff(e1,e2)) => Or(nnf(Implies(e1,e2)),nnf(Implies(e2,e1)))        
        
        case t : Terminal => t
        case u@UnaryOperator(e1,op) => op(nnf(e1))
        case b@BinaryOperator(e1,e2,op) => op(nnf(e1),nnf(e2))
        case n@NAryOperator(args,op) => op(args.map(nnf(_))) 
        
        case _ => throw IllegalStateException("Impossible event: expr did not match any case: "+inExpr)        
      }
    }
    nnf(expr)
  }

  def getClauseListener(fundef: FunDef): ((Seq[Expr], Seq[Expr], Seq[Expr]) => Unit) = {
    var counter = 0;
    val listener = (body: Seq[Expr], post: Seq[Expr], newClauses: Seq[Expr]) => {
      //reconstructs the linear constraints corresponding to each path in the programs
      //A tree is used for efficiently representing the set of constraints corresponding to each path

      //initialize the goal clauses
      if (!post.isEmpty) {
        println("Goal clauses: " + post)
        post.map(ConstraintTreeObject.addConstraint(_, false))
        println("Goal Tree: " + ConstraintTreeObject.postRoot.toString)
      }

      if (!body.isEmpty) {
        println("Body clauses: " + body)
        body.map(ConstraintTreeObject.addConstraint(_, true))
        println("Body Tree: " + ConstraintTreeObject.bodyRoot.toString)
      }      
      
      //new clauses are considered as a part of the body
      if(!newClauses.isEmpty) {      
    	println("new clauses: " + newClauses)
        newClauses.map(ConstraintTreeObject.addConstraint(_, true))
        println("Body Tree: " + ConstraintTreeObject.bodyRoot.toString)
        System.exit(0)
      }
    }
    listener
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
