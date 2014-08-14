/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.TypeTrees._

class TracingEvaluator(ctx: LeonContext, prog: Program, maxSteps: Int = 1000) extends RecursiveEvaluator(ctx, prog, maxSteps) {
  type RC = TracingRecContext
  type GC = TracingGlobalContext

  def initRC(mappings: Map[Identifier, Expr]) = TracingRecContext(mappings, 2)

  def initGC = new TracingGlobalContext(Nil)

  class TracingGlobalContext(var values: List[(Expr, Expr)]) extends GlobalContext

  case class TracingRecContext(mappings: Map[Identifier, Expr], tracingFrames: Int) extends RecContext {
    def withVars(news: Map[Identifier, Expr]) = copy(mappings = news)
  }

  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    try {
      val (res, recordedRes) = expr match {
        case Let(i,ex,b) =>
          // We record the value of the val at the position of Let, not the value of the body.
          val first = e(ex)
          val res = e(b)(rctx.withNewVar(i, first), gctx)
          (res, first)

        case fi @ FunctionInvocation(tfd, args) =>
          if (gctx.stepsLeft < 0) {
            throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
          }
          gctx.stepsLeft -= 1

          val evArgs = args.map(a => e(a))

          // build a mapping for the function...
          val frame = new TracingRecContext((tfd.params.map(_.id) zip evArgs).toMap, rctx.tracingFrames-1)

          if(tfd.hasPrecondition) {
            e(matchToIfThenElse(tfd.precondition.get))(frame, gctx) match {
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
          val callResult = e(matchToIfThenElse(body))(frame, gctx)

          if(tfd.hasPostcondition) {
            val (id, post) = tfd.postcondition.get

            val freshResID = FreshIdentifier("result").setType(tfd.returnType)
            val postBody = replace(Map(Variable(id) -> Variable(freshResID)), matchToIfThenElse(post))

            e(matchToIfThenElse(post))(frame.withNewVar(id, callResult), gctx) match {
              case BooleanLiteral(true) =>
              case BooleanLiteral(false) => throw RuntimeError("Postcondition violation for " + tfd.id.name + " reached in evaluation.")
              case other => throw EvalError(typeErrorMsg(other, BooleanType))
            }
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
          gctx.values ::= (expr -> Error(e))
        }
        throw ee;

      case re @ RuntimeError(e) =>
        if (rctx.tracingFrames > 0) {
          gctx.values ::= (expr -> Error(e))
        }
        throw re;
    }
  }

}
