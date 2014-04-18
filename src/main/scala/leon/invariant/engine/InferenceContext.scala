package leon
package invariant.engine

import purescala.Definitions._
import purescala.Trees._
import purescala._

/**
 * @author ravi
 */
class InferenceContext(
  val program : Program,    
  val leonContext : LeonContext,   
  val multfun : FunDef,
  val pivmultfun : FunDef,  
  val enumerationRelation : (Expr,Expr) => Expr,
  val modularlyAnalyze : Boolean,
  val targettedUnroll : Boolean,
  val dumpStats : Boolean ,
  val tightBounds : Boolean,
  val withmult : Boolean,
  val usereals : Boolean,
  val inferTemp : Boolean,  
  val useCegis : Boolean,
  val timeout: Int, //in secs
  val maxCegisBound : Int,
  val statsSuffix : String)  {  
  
  val reporter = leonContext.reporter
  val multOp: (Expr,Expr) => Expr = (e1, e2) => FunctionInvocation(TypedFunDef(multfun,multfun.params.map(_.tpe)), Seq(e1, e2))
}
