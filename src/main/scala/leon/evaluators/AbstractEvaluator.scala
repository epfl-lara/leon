/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Extractors.Operator
import purescala.Constructors._
import purescala.Expressions._
import purescala.Types._
import purescala.Definitions.{TypedFunDef, Program}
import purescala.DefOps
import purescala.TypeOps
import purescala.ExprOps
import purescala.Expressions.Expr
import leon.utils.DebugSectionSynthesis

/** The evaluation returns a pair (e, t),
 *  where e is the expression evaluated as much as possible, and t is the way the expression has been evaluated.
 *  Caution: If and Match statement require the condition to be non-abstract. */
class AbstractEvaluator(ctx: LeonContext, prog: Program) extends ContextualEvaluator(ctx, prog, 50000) with HasDefaultGlobalContext with HasDefaultRecContext {
  lazy val scalaEv = new ScalacEvaluator(underlying, ctx, prog)
  
  /** Evaluates resuts which can be evaluated directly
    * For example, concatenation of two string literals */
  val underlying = new DefaultEvaluator(ctx, prog)
  underlying.setEvaluationFailOnChoose(true)
  override type Value = (Expr, Expr)

  override val description: String = "Evaluates string programs but keeps the formula which generated the string"
  override val name: String = "String Tracing evaluator"

  protected def e(expr: Expr)(implicit rctx: RC, gctx: GC): (Expr, Expr) = expr match {
    case Variable(id) =>
      rctx.mappings.get(id) match {
        case Some(v) if v != expr =>
          e(v)
        case _ =>
          (expr, expr)
      }

    case e if ExprOps.isValue(e) =>
      (e, e)
      
    case IfExpr(cond, thenn, elze) =>
      val first = underlying.e(cond)
      first match {
        case BooleanLiteral(true) =>
          ctx.reporter.ifDebug(printer => printer(thenn))(DebugSectionSynthesis)
          e(thenn)
        case BooleanLiteral(false) => e(elze)
        case _ => throw EvalError(typeErrorMsg(first, BooleanType))
      }
      
    case MatchExpr(scrut, cases) =>
      val (escrut, tscrut) = e(scrut)
      val rscrut = escrut
      cases.toStream.map(c => underlying.matchesCase(rscrut, c)).find(_.nonEmpty) match {
        case Some(Some((c, mappings))) =>
          e(c.rhs)(rctx.withNewVars(mappings), gctx)
        case _ =>
          throw RuntimeError("MatchError(Abstract evaluation): "+rscrut.asString+" did not match any of the cases :\n" + cases.mkString("\n"))
      }

    case FunctionInvocation(tfd, args) =>
      if (gctx.stepsLeft < 0) {
        throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
      }
      gctx.stepsLeft -= 1
      val evArgs = args map e
      val evArgsValues = evArgs.map(_._1)
      val evArgsOrigin = evArgs.map(_._2)
      
      // build a mapping for the function...
      val frame = rctx.withNewVars(tfd.paramSubst(evArgsValues))
  
      val callResult = if ((evArgsValues forall ExprOps.isValue) && tfd.fd.annotations("extern") && ctx.classDir.isDefined) {
        (scalaEv.call(tfd, evArgsValues), functionInvocation(tfd.fd, evArgsOrigin))
      } else {
        if((!tfd.hasBody && !rctx.mappings.isDefinedAt(tfd.id)) || tfd.body.exists(b => ExprOps.exists(e => e.isInstanceOf[Choose])(b))) {
          (functionInvocation(tfd.fd, evArgsValues), functionInvocation(tfd.fd, evArgsOrigin))
        } else {
          val body = tfd.body.getOrElse(rctx.mappings(tfd.id))
          try {
            e(body)(frame, gctx)
          } catch {
            case e: RuntimeError => (functionInvocation(tfd.fd, evArgsValues), functionInvocation(tfd.fd, evArgsOrigin))
          }
        }
      }
      callResult
    case Operator(es, builder) =>
      val (ees, ts) = es.map(e).unzip
      if(ees forall ExprOps.isValue) {
        (underlying.e(builder(ees)), builder(ts))
      } else {
        (builder(ees), builder(ts))
      }
  }


}
