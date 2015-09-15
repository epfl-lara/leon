/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import purescala.Quantification._
import purescala.Types._

class TracingEvaluator(ctx: LeonContext, prog: Program, maxSteps: Int = 1000) extends RecursiveEvaluator(ctx, prog, maxSteps) {
  type RC = TracingRecContext
  type GC = TracingGlobalContext

  def initRC(mappings: Map[Identifier, Expr]) = TracingRecContext(mappings, 2)

  def initGC(model: solvers.Model) = new TracingGlobalContext(Nil, model)

  class TracingGlobalContext(var values: List[(Tree, Expr)], model: solvers.Model) extends GlobalContext(model)

  case class TracingRecContext(mappings: Map[Identifier, Expr], tracingFrames: Int) extends RecContext {
    def newVars(news: Map[Identifier, Expr]) = copy(mappings = news)
  }

  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    try {
      val (res, recordedRes) = expr match {
        case Let(i,ex,b) =>
          // We record the value of the val at the position of Let, not the value of the body.
          val first = e(ex)
          val res = e(b)(rctx.withNewVar(i, first), gctx)
          (res, first)

        case p: Passes =>
           val r = e(p.asConstraint)
           (r, r)

        case MatchExpr(scrut, cases) =>
          val rscrut = e(scrut)

          val r = cases.toStream.map(c => matchesCase(rscrut, c)).find(_.nonEmpty) match {
            case Some(Some((c, mappings))) =>
              gctx.values ++= (Map(c.pattern -> rscrut) ++ mappings.map { case (id, v) => id.toVariable.setPos(id) -> v })

              e(c.rhs)(rctx.withNewVars(mappings), gctx)
            case _ =>
              throw RuntimeError("MatchError: "+rscrut+" did not match any of the cases")
          }

          (r, r)

        case fi @ FunctionInvocation(tfd, args) =>
          if (gctx.stepsLeft < 0) {
            throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
          }
          gctx.stepsLeft -= 1

          val evArgs = args.map(a => e(a))

          // build a mapping for the function...
          val frame = new TracingRecContext(tfd.paramSubst(evArgs), rctx.tracingFrames-1)

          if(tfd.hasPrecondition) {
            e(tfd.precondition.get)(frame, gctx) match {
              case BooleanLiteral(true) =>
              case BooleanLiteral(false) =>
                throw RuntimeError("Precondition violation for " + tfd.id.name + " reached in evaluation.: " + tfd.precondition.get)
              case other => throw RuntimeError(typeErrorMsg(other, BooleanType))
            }
          }

          if(!tfd.hasBody && !rctx.mappings.isDefinedAt(tfd.id)) {
            throw EvalError("Evaluation of function with unknown implementation.")
          }

          val body = tfd.body.getOrElse(rctx.mappings(tfd.id))
          val callResult = e(body)(frame, gctx)

          tfd.postcondition match {
            case Some(post) =>

              e(Application(post, Seq(callResult)))(frame, gctx) match {
                case BooleanLiteral(true) =>
                case BooleanLiteral(false) => throw RuntimeError("Postcondition violation for " + tfd.id.name + " reached in evaluation.")
                case other => throw EvalError(typeErrorMsg(other, BooleanType))
              }
            case None =>
          }

          (callResult, callResult)
        case _ =>
          val res = super.e(expr)
          (res, res)
      }
      if (rctx.tracingFrames > 0) {
        gctx.values ::= (expr -> recordedRes)
      }

      res
    } catch {
      case ee @ EvalError(e) =>
        if (rctx.tracingFrames > 0) {
          gctx.values ::= (expr -> Error(expr.getType, e))
        }
        throw ee;

      case re @ RuntimeError(e) =>
        if (rctx.tracingFrames > 0) {
          gctx.values ::= (expr -> Error(expr.getType, e))
        }
        throw re;
    }
  }

}
