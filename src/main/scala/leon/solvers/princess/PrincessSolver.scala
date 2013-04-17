/*package leon
package solvers.princess

//princess imports
import ap._
import ap.parser._
import IExpression._
import SimpleAPI.ProverStatus

import leon.solvers.Solver

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._

import evaluators._

import termination._

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}

class PrincessSolver(context : LeonContext)
  /*extends Solver(context)     
     with LeonComponent */ {

  enclosing =>

  val name = "Princess"
  val description = "Princess Solver"

  /*override val definedOptions : Set[LeonOptionDef] = Set(
    LeonFlagOptionDef("evalground",         "--evalground",         "Use evaluator on functions applied to ground arguments"),
    LeonFlagOptionDef("checkmodels",        "--checkmodels",        "Double-check counter-examples with evaluator"),
    LeonFlagOptionDef("feelinglucky",       "--feelinglucky",       "Use evaluator to find counter-examples early"),
    LeonFlagOptionDef("codegen",            "--codegen",            "Use compiled evaluator instead of interpreter"),
    LeonFlagOptionDef("fairz3:unrollcores", "--fairz3:unrollcores", "Use unsat-cores to drive unrolling while remaining fair")
  )*/
    
  /*override def getNewSolver{
    new 
  }
 
  override def setProgram(prog : Program) {
    super.setProgram(prog)
  }
   
  override def solve(leonFormula: Expr) = {
    context.reporter.warning("Calling Solve method on princess solver")    
    None
  }  

  override def solveSAT(vc : Expr) : (Option[Boolean],Map[Identifier,Expr]) = {
    context.reporter.warning("Calling solveSAT method on princess solver")
    (None,Map[Identifier,Expr]())
  }
  
  
  override def solveSATWithCores(expression: Expr, assumptions: Set[Expr]) = {
    context.reporter.warning("Calling solveSATWithCores method on princess solver")
    (None,Map[Identifier,Expr](),Set[Expr]())
  }
*/  
  def getInterpolants(parts : List[(FunDef,List[Expr])], leonExprs :List[Expr]) : List[Expr] ={
    val p = SimpleAPI(true, true)
    
    p.scope {
      p.setConstructProofs(true)

      //declare the list of free variables (consider only integers for now)
      val freevars = variablesOf(And(leonExprs))     
      val freevarMap = freevars.foldLeft(Map[Identifier,IExpression]())((g,id) => id.getType match {
        case Int32Type => g + (id -> p.createConstant)
        case BooleanType => g + (id -> p.createBooleanVariable)
        case _ => g
      })
      
      //add partitions
      var partcount = 0
	  var processedFormulas = List[Expr]()
	  var partnames = List[String]()
	  	  
	  parts.foreach((elem) => {
	    val (func,list) = elem	    
	    
	    val formulas = list -- processedFormulas
	    
	    p.setPartitionNumber(partcount) 
	    getPrincessFormula(And(formulas),freevarMap) match {
	      case Some(v) => { 
	        (p !! v.asInstanceOf[IFormula]) 
	        println("Adding assertion: "+v) 
	      }
	      case _ => context.reporter.warning("cannot convert to princess formula: "+formulas)
	    }
	   	    
	    //update mutable state variables
	    processedFormulas ++= formulas	    
	    partcount += 1
	  })
	 	  
	  //add the final part
	  val leftFormula = leonExprs -- processedFormulas
	  p.setPartitionNumber(partcount)
	  getPrincessFormula(Not(And(leftFormula)),freevarMap) match {
	      case Some(v) => { 
	        p !! v.asInstanceOf[IFormula]
	        println("Adding assertion: "+v)
	      }
	      case _ => context.reporter.warning("cannot convert to princess formula: "+leftFormula)
	   }	  
	   
	   /*//add interpolant blocks	   
	   for( i <- 1 to partnames.length - 1 )  {
	      val (phrase,index) = partnames.foldLeft((new String(),1))(
	      (g,x) => {	      
	    	  	val (ipstr,index) = g
	    	  	if(index == i + 1 && index > 1) (ipstr + ";" + x, index + 1)
	    	  	else if(index > 1) (ipstr + "," + x, index + 1)
	    	  	else (x, index + 1)
	      	})	  	    
	   }*/
      //construct a seq (of sets) from 0 to partcount
      var partseq = Seq[Set[Int]]()
      for( i <- 0 to partcount ) { partseq :+= Set(i) }
            
      
	  println(p???)  // Unsat
	  println(p.getInterpolants(partseq))
	  //println(p.getInterpolants(partseq))
	  List[Expr]()
	}
  }
  
  ///Caution: this uses ugly type casts to handle the overly complicated formula types of princess
  /** 
   * create a function to convert leon expressions into princess formulas (not all operations are supported)
   * note: princess does not support boolean type. Hence, we need to replace boolean variables by a predicate
   * which may introduce disjunctions 
   **/
  def getPrincessFormula(leonExpr: Expr, freevarMap : Map[Identifier,IExpression]) : Option[IExpression] = {
    	  
	  leonExpr match {
	    case And(args) => Some(and(args.collect(getPrincessFormula(_,freevarMap) match { case Some(v) => v.asInstanceOf[IFormula]})))
	    case Or(args) => Some(or(args.collect(getPrincessFormula(_,freevarMap) match { case Some(v) => v.asInstanceOf[IFormula]})))

	    case Variable(id) => id.getType match {
	    							case Int32Type => Some(freevarMap.get(id).get)
	    							//case BooleanType => Some(freevarMap.get(id).get)
	    							case _ => None
	    						}
	    case IntLiteral(v) => Some(i(v))
	    case BooleanLiteral(v) => Some(i(v))	    
	    
	    case t@Not(Variable(id)) => context.reporter.warning("Encountered negation of a variable: " + t); None
	    case Not(t) => getPrincessFormula(t,freevarMap) match { 
	      case Some(v) => Some(!(v.asInstanceOf[IFormula]))
	      case _ => None
	    }
	    
	    case UMinus(t) => getPrincessFormula(t,freevarMap) match { 
	      case Some(v) => Some(-(v.asInstanceOf[ITerm]))
	      case _ => None
	    }
	    	    	   
	    case t@Iff(t1,t2) => (t1,t2) match {
	      case (Variable(id),Variable(id2)) => None
	      case (Variable(id),t2) => getPrincessFormula(t2,freevarMap) 	      
	      case (t1,Variable(id)) => getPrincessFormula(t1,freevarMap)
	      case _ => None
	    } 
	    
	    /*(getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match {	      
	      	case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[IFormula] <=> v2.asInstanceOf[IFormula])
	      	case _ => None
	      }*/
	    
	    case Implies(t1,t2) => (getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[IFormula] ==> v2.asInstanceOf[IFormula])
	      case _ => None
	    }
	    
	    case Equals(t1,t2) => //replace equalities by inequalities 
	      //getPrincessFormula(And(LessEquals(t1,t2),GreaterEquals(t1,t2)),freevarMap)	      
	      (getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      		case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[ITerm] === v2.asInstanceOf[ITerm])
	      		case _ => None
	    	}
	      
	    case Plus(t1,t2) => (getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[ITerm] + v2.asInstanceOf[ITerm])
	      case _ => None
	    }
	    case Minus(t1,t2) => (getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[ITerm] - v2.asInstanceOf[ITerm])
	      case _ => None
	    }
	    case Times(t1,t2) => (getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[ITerm] * v2.asInstanceOf[ITerm])
	      case _ => None
	    }
	    case LessThan(t1,t2) => (getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[ITerm] < v2.asInstanceOf[ITerm])
	      case _ => None
	    }
	    case GreaterThan(t1,t2) => (getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[ITerm] > v2.asInstanceOf[ITerm])
	      case _ => None
	    }
	    case LessEquals(t1,t2) => (getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[ITerm] <= v2.asInstanceOf[ITerm])
	      case _ => None
	    }
	    case GreaterEquals(t1,t2) => (getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[ITerm] >= v2.asInstanceOf[ITerm])
	      case _ => None
	    }	    
	    case _ => None
	  }
  }

  /*override def halt() {
    super.halt    
  }*/
}*/

//some code dealing with princess
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
