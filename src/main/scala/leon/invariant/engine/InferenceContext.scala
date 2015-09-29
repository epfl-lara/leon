package leon
package invariant.engine

import purescala.Definitions._
import purescala.Expressions._
import purescala._

/**
 * @author ravi
 */
case class InferenceContext(
  val program : Program,
  val toVerifyPostFor: Set[String],
  val leonContext : LeonContext,
  val multOp: (Expr,Expr) => Expr,
  val enumerationRelation : (Expr,Expr) => Expr,
  val modularlyAnalyze : Boolean,
  val targettedUnroll : Boolean,
  val autoInference : Boolean,
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
}
