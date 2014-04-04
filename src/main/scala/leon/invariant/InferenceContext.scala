package leon
package invariant

import leon.LeonContext
import leon.Reporter
import leon.purescala.Definitions._
import leon.purescala.Trees._
/**
 * @author ravi
 */
class InferenceContext(
  val program : Program,    
  val leonContext : LeonContext, 
  val timeout: Int, //in secs
  val multfun : FunDef,
  val pivmultfun : FunDef,  
  val enumerationRelation : (Expr,Expr) => Expr,
  val modularlyAnalyze : Boolean,
  val targettedUnroll : Boolean,
  val dumpStats : Boolean ,
  val tightBounds : Boolean,
  val withmult : Boolean,
  val inferTemp : Boolean,  
  val useCegis : Boolean,    
  val maxCegisBound : Int,
  val statsSuffix : String)  {  
  
  val reporter = leonContext.reporter
  val multOp: (Expr,Expr) => Expr = (e1, e2) => FunctionInvocation(multfun, Seq(e1, e2))
}
