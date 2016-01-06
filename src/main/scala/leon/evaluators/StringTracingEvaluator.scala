/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Extractors.Operator
import purescala.Expressions._
import purescala.Types._
import purescala.Definitions.Program
import purescala.Expressions.Expr
import leon.utils.DebugSectionSynthesis

class StringTracingEvaluator(ctx: LeonContext, prog: Program) extends ContextualEvaluator(ctx, prog, 50000) with HasDefaultGlobalContext with HasDefaultRecContext {

  val underlying = new DefaultEvaluator(ctx, prog) {
    override protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
      case FunctionInvocation(tfd, args) =>
        if (gctx.stepsLeft < 0) {
          throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
        }
        gctx.stepsLeft -= 1
  
        val evArgs = args map e
  
        // build a mapping for the function...
        val frame = rctx.withNewVars(tfd.paramSubst(evArgs))
    
        val callResult = if (tfd.fd.annotations("extern") && ctx.classDir.isDefined) {
          scalaEv.call(tfd, evArgs)
        } else {
          if(!tfd.hasBody && !rctx.mappings.isDefinedAt(tfd.id)) {
            throw EvalError("Evaluation of function with unknown implementation.")
          }
  
          val body = tfd.body.getOrElse(rctx.mappings(tfd.id))
          e(body)(frame, gctx)
        }
  
        callResult
      
      case Variable(id) =>
        rctx.mappings.get(id) match {
          case Some(v) if v != expr =>
            e(v)
          case Some(v) =>
            v
          case None =>
            expr
        }
      case StringConcat(s1, s2) =>
        val es1 = e(s1)
        val es2 = e(s2)
        (es1, es2) match {
          case (StringLiteral(_), StringLiteral(_)) =>
            (super.e(StringConcat(es1, es2)))
          case _ =>
            StringConcat(es1, es2)
        }
      case StringEscape(a) =>
        val ea = e(a)
        ea match {
          case StringLiteral(_) => super.e(StringEscape(a))
          case _ => StringEscape(ea)
        }
      case expr =>
        super.e(expr)
    }
  }
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
      
    case StringEscape(a) =>
      val (ea, ta) = e(a)
      ea match {
        case StringLiteral(_) => (underlying.e(StringEscape(ea)), StringEscape(ta))
        case _ => (StringEscape(ea), StringEscape(ta))
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
      (underlying.e(builder(ees)), builder(ts))

  }


}
