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
  
  def ConvertToPrincessFormat(parts: List[(FunDef,List[Expr])], formula: Expr)
  {
	  
  }

}
