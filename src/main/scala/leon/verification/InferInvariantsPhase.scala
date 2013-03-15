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
  //private var 

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("timeout",   "--timeout=T",       "Timeout after T seconds when trying to prove a verification condition.")
  )

  def run(ctx: LeonContext)(program: Program) : VerificationReport = {       
    
    val reporter = ctx.reporter
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
		   println("Final Guard: " + guard) 
//		   println("Value: "+value)		   
		   		   
		   //convert the guards to princess input
		   ConvertToPrincessFormat(parts,guard)
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
	    case _ => ;
	  })
	  println("}")
	  
	  //create a function to convert leon expressions into princess formulas (not all operations are supported)
	  def PrinForm(formula: Expr) : String = formula match {
	    case And(args) => args.foldLeft(new String())((str,x) => {
	    	val r = PrinForm(x)	    	
	    	str + (if(r.isEmpty()) "" 
	    	  else if(str.isEmpty()) r
	    	  else " & "+r)
	    })
	    case Or(args) => args.foldLeft(new String())((str,x) => str + " | " + PrinForm(x))
	    case Variable(id) => id.getType match {
	    							case Int32Type => id.toString
	    							case _ => ""
	    						}
	    case IntLiteral(v) => v.toString
	    case BooleanLiteral(v) => v.toString	    
	    case Not(t) => "!("+PrinForm(t)+")"
	    case UMinus(t) => "-("+PrinForm(t)+")"
	    case Equals(t1,t2) => PrinForm(t1) + "=" + PrinForm(t2)
	    case Iff(t1,t2) => PrinForm(Implies(t1,t2)) + PrinForm(Implies(t2,t1))  
	    case Implies(t1,t2) => PrinForm(Or(Not(t1),t2))
	    case t@Plus(t1,t2) => t.toString
	    case t@Minus(t1,t2) => t.toString
	    case t@Times(t1,t2) => t.toString
	    case t@Division(t1,t2) => t.toString
	    case t@Modulo(t1,t2) => t.toString
	    case t@LessThan(t1,t2) => t.toString
	    case t@GreaterThan(t1,t2) => t.toString
	    case t@LessEquals(t1,t2) => t.toString
	    case t@GreaterEquals(t1,t2) => t.toString	    
	    case _ => "" //empty string in other cases
	  }
	  
	  //create formula parts
	  println("\\problem{")
	  var processedFormulas = List[Expr]()
	  var partnames = List[String]()
	  
	  parts.foreach((elem) => {
	    val (func,list) = elem	    
	    val formulas = list -- processedFormulas
	    print("\\part["+func.id+"]"+"\t")
	    println("(" + PrinForm(And(formulas)) +") &")
	    processedFormulas = processedFormulas ++ formulas
	    partnames = partnames :+ func.id.toString
	  })
	  
	  //add the implies block
	  println("->")
	  
	  //add the final part
	   val leftFormula = guard -- processedFormulas	   
	   print("\\part[assert]"+"\t")
	   println("(" + PrinForm(And(leftFormula)) +")")
	   
	   //add interpolant blocks	   
	   for( i <- 0 to parts.length )  {
	     val str2 = partnames.foldLeft((new String(),0))((g,x) => if(g._2 == i + 1 && g._2 > 1) (g._1 + ";" + x,g._2+1) 
	    		 													else (g._1 + "," + x,g._2 + 1))._1
	    println("\\interpolant {"+str2+"}")
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
