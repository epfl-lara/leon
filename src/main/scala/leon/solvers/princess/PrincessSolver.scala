package leon
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
  extends Solver(context)     
     with LeonComponent {

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
  
  
  def solveSATWithCores(expression: Expr, assumptions: Set[Expr]) = {
    context.reporter.warning("Calling solveSATWithCores method on princess solver")
    (None,Map[Identifier,Expr](),Set[Expr]())
  }
  
  def getInterpolants(parts : List[(FunDef,List[Expr])], leonExprs :List[Expr]) : List[Expr] ={
    val p = SimpleAPI.spawnWithAssertions
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
	    p !! getPrincessFormula(And(formulas),freevarMap).asInstanceOf[IFormula]
	   	    
	    //update mutable state variables
	    processedFormulas ++= formulas	    
	    partcount += 1
	  })
	 	  
	  //add the final part
	  val leftFormula = leonExprs -- processedFormulas
	  p.setPartitionNumber(partcount)
	  p !! getPrincessFormula(Not(And(leftFormula)),freevarMap).asInstanceOf[IFormula]
	   
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
	    							case BooleanType => Some(freevarMap.get(id).get)
	    							case _ => None
	    						}
	    case IntLiteral(v) => Some(i(v))
	    case BooleanLiteral(v) => Some(i(v))	    
	    
	    case t@Not(Variable(id)) => context.reporter.warning("Encountered negation of a variable: " + t); None
	    case Not(t) => getPrincessFormula(t,freevarMap) match { 
	      case Some(v) => Some(INot(v.asInstanceOf[IFormula]))
	      case _ => None
	    }
	    
	    case UMinus(t) => getPrincessFormula(t,freevarMap) match { 
	      case Some(v) => Some(-(v.asInstanceOf[ITerm]))
	      case _ => None
	    }
	    	    	   
	    case t@Iff(t1,t2) => (getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[IFormula] <=> v2.asInstanceOf[IFormula])
	      case _ => None
	    }
	      	     				
	    case t@Iff(t1,t2) => (getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[IFormula] ==> v2.asInstanceOf[IFormula])
	      case _ => None
	    }
	    
	    case Equals(t1,t2) => //replace equalities by inequalities 
	      getPrincessFormula(And(LessEquals(t1,t2),GreaterEquals(t1,t2)),freevarMap)
	      
	      /*(getPrincessFormula(t1,freevarMap),getPrincessFormula(t2,freevarMap)) match { 
	      		case (Some(v1),Some(v2)) => Some(v1.asInstanceOf[ITerm] == v2.asInstanceOf[ITerm])
	      		case _ => None
	    	}*/
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

  override def halt() {
    super.halt    
  }
}
