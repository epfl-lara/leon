package leon.purescala

import leon.evaluators.StringTracingEvaluator
import leon.purescala
import purescala.Definitions.Program
import leon.evaluators.StringTracingEvaluator
import purescala.Expressions._
import purescala.Types.StringType
import leon.utils.DebugSectionSynthesis
import leon.utils.DebugSectionVerification
import leon.purescala.Quantification._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Expressions.{Pattern, Expr}
import purescala.Extractors._
import purescala.TypeOps._
import purescala.Types._
import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import purescala.SelfPrettyPrinter
import leon.solvers.{ HenkinModel, Model, SolverFactory }
import leon.LeonContext
import leon.evaluators

/** This pretty-printer uses functions defined in Leon itself.
  * If not pretty printing function is defined, return the default value instead
  * @param The list of functions which should be excluded from pretty-printing (to avoid rendering counter-examples of toString methods using the method itself)
  * @return a user defined string for the given typed expression. */
object SelfPrettyPrinter {
  def print(v: Expr, orElse: =>String, excluded: FunDef => Boolean = Set())(implicit ctx: LeonContext, program: Program): String = {
    (program.definedFunctions find {
      case fd if !excluded(fd) =>
        fd.returnType == StringType && fd.params.length == 1 && TypeOps.isSubtypeOf(v.getType, fd.params.head.getType) && fd.id.name.toLowerCase().endsWith("tostring") &&
        program.callGraph.transitiveCallees(fd).forall { fde => 
          !purescala.ExprOps.exists( _.isInstanceOf[Choose])(fde.fullBody)
        }
    }) match {
      case Some(fd) =>
        //println("Found fd: " + fd.id.name)
        val ste = new StringTracingEvaluator(ctx, program)
        try {
        val result = ste.eval(FunctionInvocation(fd.typed, Seq(v)))
        
        result.result match {
          case Some((StringLiteral(res), _)) if res != "" =>
            res
          case _ =>
            orElse
        }
        } catch {
          case e: evaluators.ContextualEvaluator#EvalError =>
            orElse
        }
      case None =>
        orElse
    }
  }
}