/* Copyright 2009-2015 EPFL, Lausanne */

package leon.repair

import leon.purescala._
import Definitions._
import Expressions._
import Types._
import ExprOps.postMap
import Constructors.not
import leon.LeonContext
import leon.evaluators.DefaultEvaluator
import scala.util.Try

// This evaluator treats the condition cond non-deterministically in the following sense:
// If a function invocation fails or violates a postcondition for cond, 
// it backtracks and gets executed again for !cond
class RepairNDEvaluator(ctx: LeonContext, prog: Program, fd : FunDef, cond: Expr) extends DefaultEvaluator(ctx, prog) {
    
  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
 
    case FunctionInvocation(tfd, args) if tfd.fd == fd =>
      if (gctx.stepsLeft < 0) {
        throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
      }
      gctx.stepsLeft -= 1

      val evArgs = args.map(a => e(a))

      // build a mapping for the function...
      val frame = rctx.newVars((tfd.params.map(_.id) zip evArgs).toMap)
      
      if(tfd.hasPrecondition) {
        e(tfd.precondition.get)(frame, gctx) match {
          case BooleanLiteral(true) =>
          case BooleanLiteral(false) =>
            throw RuntimeError("Precondition violation for " + tfd.id.name + " reached in evaluation.: " + tfd.precondition.get)
          case other =>
            throw RuntimeError(typeErrorMsg(other, BooleanType))
        }
      }

      if(!tfd.hasBody && !rctx.mappings.isDefinedAt(tfd.id)) {
        throw EvalError("Evaluation of function with unknown implementation.")
      }

      val body = tfd.body.getOrElse(rctx.mappings(tfd.id))
      
      def treat(subst : Expr => Expr) = {
        val callResult = e(subst(body))(frame, gctx)
  
        tfd.postcondition match {
          case Some(post) =>
            e(subst(Application(post, Seq(callResult))))(frame, gctx) match {
              case BooleanLiteral(true) =>
              case BooleanLiteral(false) => throw RuntimeError("Postcondition violation for " + tfd.id.name + " reached in evaluation.")
              case other => throw EvalError(typeErrorMsg(other, BooleanType))
            }
          case None =>
        }
  
        callResult
      }
    
      Try {
        treat(e => e)
      }.getOrElse {
        treat( postMap {
          // Use reference equality, just in case cond appears again in the program
          case c if c eq cond => Some(not(cond))
          case _ => None
        })
      }
      
    case _ => super.e(expr)     
  }

  
  
  
}
