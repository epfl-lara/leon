package leon
package invariant

import leon.LeonContext
import leon.Reporter
import leon.purescala.Definitions.Program
import leon.purescala.Trees._
/**
 * @author ravi
 */
class InferenceContext(
  val program : Program,    
  val context : LeonContext, 
  val timeout: Int, //in secs
  val multOp : ((Expr,Expr) => Expr),
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
  
  val reporter = context.reporter
}
