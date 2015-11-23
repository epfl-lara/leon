/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Extractors.Operator
import purescala.Expressions._
import purescala.Types._
import purescala.Definitions.Program
import purescala.Expressions.Expr
import leon.utils.DebugSectionSynthesis

class StringTracingEvaluator(ctx: LeonContext, prog: Program) extends ContextualEvaluator(ctx, prog, 50000) with DefaultContexts {

  val underlying = new DefaultEvaluator(ctx, prog)
  override type Value = (Expr, Expr)

  override val description: String = "Evaluates string programs but keeps the formula which generated the string"
  override val name: String = "String Tracing evaluator"

  protected def e(expr: Expr)(implicit rctx: RC, gctx: GC): (Expr, Expr) = expr match {
    case Variable(id) =>
      rctx.mappings.get(id) match {
        case Some(v) if v != expr =>
          e(v)
        case Some(v) =>
          (v, expr)
        case None =>
          (expr, expr)
      }
      
    case StringConcat(s1, s2) =>
      val (es1, t1) = e(s1)
      val (es2, t2) = e(s2)
      (es1, es2) match {
        case (StringLiteral(_), StringLiteral(_)) =>
          (underlying.e(StringConcat(es1, es2)), StringConcat(t1, t2))
        case _ =>
          (StringConcat(es1, es2), StringConcat(t1, t2))
      }
    case StringLength(s1) => 
      val (es1, t1) = e(s1)
      es1 match {
        case StringLiteral(_) =>
          (underlying.e(StringLength(es1)), StringLength(t1))
        case _ =>
          (StringLength(es1), StringLength(t1))
      }

    case expr@StringLiteral(s) => 
      (expr, expr)
      
    case IfExpr(cond, thenn, elze) =>
      val first = underlying.e(cond)
      first match {
        case BooleanLiteral(true) =>
          ctx.reporter.ifDebug(printer => printer(thenn))(DebugSectionSynthesis)
          e(thenn)
        case BooleanLiteral(false) => e(elze)
        case _ => throw EvalError(typeErrorMsg(first, BooleanType))
      }

    case Operator(es, builder) =>
      val (ees, ts) = es.map(e).unzip
      ctx.reporter.debug("Going to evaluate this : " + builder(ees))(DebugSectionSynthesis)
      (underlying.e(builder(ees)), builder(ts))
  }


}
