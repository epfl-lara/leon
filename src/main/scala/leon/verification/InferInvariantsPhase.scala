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
    
    reporter = ctx.reporter
    val functionsToAnalyse : MutableSet[String] = MutableSet.empty
    var timeout: Option[Int] = None    

    for(opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        functionsToAnalyse ++= fs

      case v @ LeonValueOption("timeout", _) =>
        timeout = v.asInt(ctx)

      case _ =>
    }
    
    /**
     * This function will be called back by the Leon verifier.
     */
    val ProcessNewInput = (input : Map[Identifier,Expr], formula: Expr)  => {
    //compute the symbolic trace induced by the input    
	 val evalRes = new TraceCollectingEvaluator(ctx,program).eval(formula,input)
	 evalRes match {
	   case EvaluationWithPartitions(cval,SymVal(guard,value),parts) => {
		   println("Concrete Value: "+ cval)		   
		   //print guards for each method
		   parts.foreach((x) => { println("Method: "+x._1.id+" Guard: "+x._2) })
		   
		   //construct the path condition
		   val pathcond = (guard :+ value)
		   println("Final Guard: " + pathcond) 
		   		   
		   //convert the guards to princess input
		   ConvertToPrincessFormat(parts,pathcond)
	   }
	   case _ => reporter.warning("No solver could prove or disprove the verification condition.") 
	 }	 
    }
    
    reporter.info("Running Invariant Inference Phase...")       
    
    //invoking leon verifier 
    var report = AnalysisPhase.runner(ctx)(program,Some(ProcessNewInput))
    
    report   
  }
  
  def ConvertToPrincessFormat(parts: List[(FunDef,List[Expr])], guard: List[Expr])
  {
	  //declare the list of free variables (consider only integers for now)
	  val freevars = variablesOf(And(guard))
	  println("\\function{")
	  freevars.foreach((id) => id.getType match {
	    case Int32Type => println("int "+id.toString)
	    case BooleanType => ;//reporter.warning("Boolean types present not handling them for now ")
	    case _ => ;
	  })
	  println("}")
	  
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
	  println("\\problem{")
	  var partcount = 0
	  var processedFormulas = List[Expr]()
	  var partnames = List[String]()
	  
	  parts.foreach((elem) => {
	    val (func,list) = elem	    
	    
	    val formulas = list -- processedFormulas
	    val partstr = func.id.toString() + partcount
	    print("\\part["+ partstr  +"]"+"\t")
	    println("(" + PrinForm(And(formulas)) +") &")
	    
	    //update mutable state variables
	    processedFormulas = processedFormulas ++ formulas
	    partnames = partnames :+ partstr
	    partcount = partcount + 1
	  })
	  
	  //add the implies block
	  println("->")
	  
	  //add the final part
	   val leftFormula = guard -- processedFormulas	   
	   print("\\part[assert]"+"\t")
	   println("(" + PrinForm(And(leftFormula)) +")")
	   
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
	      println("\\interpolant {"+phrase+"}")	     
	   }
	    
/*	  \problem {
   Problem to be proven and interpolated 

  \part[cond]          (a-2*x = 0 & -a <= 0) &
  \part[par1]	    	(2*b - a <=0 & -2*b + a -1 <=0) & 
  \part[par2] 		(c-3*b-1=0)
  \part[par5]		par1 | par2 
                       ->
  \part[assert]        c > a
}

 Interpolation specification 
\interpolant {cond, par1, par2; assert}*/
  }

}
