/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.TypeTrees._

class TracingEvaluator(ctx: LeonContext, prog: Program) extends RecursiveEvaluator(ctx, prog) {
  type RC = TracingRecContext
  type GC = TracingGlobalContext

  var lastGlobalContext: Option[GC] = None

  def initRC(mappings: Map[Identifier, Expr]) = {
    TracingRecContext(mappings, 2)
  }

  def initGC = {
    val gc = new TracingGlobalContext(stepsLeft = 50000, Nil)
    lastGlobalContext = Some(gc)
    gc
  }

  class TracingGlobalContext(stepsLeft: Int, var values: List[(Expr, Expr)]) extends GlobalContext(stepsLeft)

  case class TracingRecContext(mappings: Map[Identifier, Expr], tracingFrames: Int) extends RecContext {
    def withNewVar(id: Identifier, v: Expr) = copy(mappings = mappings + (id -> v))

    def withVars(news: Map[Identifier, Expr]) = copy(mappings = news)
  }

  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    try {
      val (res, recordedRes) = expr match {
        case Let(i,e,b) =>
          // We record the value of the val at the position of Let, not the value of the body.
          val first = se(e)
          val res = se(b)(rctx.withNewVar(i, first), gctx)
          (res, first)

        case fi @ FunctionInvocation(fd, args) =>

          val evArgs = args.map(a => se(a))

          // build a mapping for the function...
          val frame = new TracingRecContext((fd.args.map(_.id) zip evArgs).toMap, rctx.tracingFrames-1)

          if(fd.hasPrecondition) {
            se(matchToIfThenElse(fd.precondition.get))(frame, gctx) match {
              case BooleanLiteral(true) =>
              case BooleanLiteral(false) =>
                throw RuntimeError("Precondition violation for " + fd.id.name + " reached in evaluation.: " + fd.precondition.get)
              case other => throw RuntimeError(typeErrorMsg(other, BooleanType))
            }
          }

          if(!fd.hasBody && !rctx.mappings.isDefinedAt(fd.id)) {
            throw EvalError("Evaluation of function with unknown implementation.")
          }

          val body = fd.body.getOrElse(rctx.mappings(fd.id))
          val callResult = se(matchToIfThenElse(body))(frame, gctx)

          if(fd.hasPostcondition) {
            val (id, post) = fd.postcondition.get

            val freshResID = FreshIdentifier("result").setType(fd.returnType)
            val postBody = replace(Map(Variable(id) -> Variable(freshResID)), matchToIfThenElse(post))

            se(matchToIfThenElse(post))(frame.withNewVar(id, callResult), gctx) match {
              case BooleanLiteral(true) =>
              case BooleanLiteral(false) => throw RuntimeError("Postcondition violation for " + fd.id.name + " reached in evaluation.")
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
