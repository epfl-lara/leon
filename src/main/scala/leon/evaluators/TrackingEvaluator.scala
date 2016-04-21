/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Types._

import scala.collection.mutable.{Map => MMap}

/** An [[Evaluator]] that tracks information about the runtime call tree.
  * Transitive dependencies between function calls are stored in [[fullCallGraph]].
  * Additionally, [[fiStatus]] tracks if each function invocation was successful or erroneous (led to an error).
  */
class TrackingEvaluator(ctx: LeonContext, prog: Program) extends RecursiveEvaluator(ctx, prog, 50000) with HasDefaultGlobalContext {
  type RC = CollectingRecContext

  def initRC(mappings: Map[Identifier, Expr]) = CollectingRecContext(mappings, None)
  
  type FI = (FunDef, Seq[Expr])
  
  // This is a call graph to track dependencies of function invocations.
  // If fi1 calls fi2 but fails fi2's precondition, we consider it 
  // fi1's fault and we don't register the dependency.
  private val callGraph : MMap[FI, Set[FI]] = MMap()
  // Register a call without any edges towards other calls
  private def registerNode(fi : FI) = if (!callGraph.contains(fi)) callGraph update (fi, Set())
  // Register an edge - also registers start and end nodes
  private def registerCall(fi : FI, lastFI : Option[FI]) = {
    lastFI foreach { lfi => 
      callGraph update (lfi, callGraph(lfi) + fi) 
    }
  }
  def fullCallGraph = leon.utils.GraphOps.transitiveClosure(callGraph.toMap)
  
  // Tracks if every function invocation succeeded or failed
  private val fiStatus_ : MMap[FI, Boolean] = MMap().withDefaultValue(false)
  private def registerSuccessful(fi : FI) = fiStatus_ update (fi, true )
  private def registerFailed    (fi : FI) = fiStatus_ update (fi, false)
  def fiStatus = fiStatus_.toMap.withDefaultValue(false)
  
  case class CollectingRecContext(mappings: Map[Identifier, Expr], lastFI : Option[FI]) extends RecContext[CollectingRecContext] {
    def newVars(news: Map[Identifier, Expr]) = copy(news, lastFI)
    def withLastFI(fi : FI) = copy(lastFI = Some(fi))
  }
  
  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case FunctionInvocation(tfd, args) =>
      if (gctx.stepsLeft < 0) {
        throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
      }
      gctx.stepsLeft -= 1
      
      val evArgs = args.map(a => e(a))
      
      // build a mapping for the function...
      val frameBlamingCaller = rctx.newVars(tfd.paramSubst(evArgs))
      
      if(tfd.hasPrecondition) {
        e(tfd.precondition.get)(frameBlamingCaller, gctx) match {
          case BooleanLiteral(true) => 
            // We consider this function invocation successful, unless the opposite is proven.
            registerSuccessful(tfd.fd, evArgs)
            // Only register a call dependency if the call we depend on does not fail precondition
            registerCall((tfd.fd, evArgs), rctx.lastFI)
            registerNode((tfd.fd, evArgs))
          case BooleanLiteral(false) =>
            // Caller's fault!
            rctx.lastFI foreach registerFailed
            throw RuntimeError("Precondition violation for " + tfd.id.name + " reached in evaluation.: " + tfd.precondition.get)
          case other =>
            // Caller's fault!
            rctx.lastFI foreach registerFailed
            throw RuntimeError(typeErrorMsg(other, BooleanType))
        }
      } else {
        registerSuccessful(tfd.fd, evArgs)
        registerNode((tfd.fd, evArgs))
        registerCall((tfd.fd, evArgs), rctx.lastFI)
      }

      if(!tfd.hasBody && !rctx.mappings.isDefinedAt(tfd.id)) {
        throw EvalError("Evaluation of function with unknown implementation.")
      }

      val body = tfd.body.getOrElse(rctx.mappings(tfd.id))

      val frameBlamingCallee = frameBlamingCaller.withLastFI(tfd.fd, evArgs)
      
      val callResult = e(body)(frameBlamingCallee, gctx)

      tfd.postcondition match {
        case Some(post) => 
          e(Application(post, Seq(callResult)))(frameBlamingCallee, gctx) match {
            case BooleanLiteral(true) =>
            case BooleanLiteral(false) =>
              // Callee's fault
              registerFailed(tfd.fd, evArgs)
              throw RuntimeError("Postcondition violation for " + tfd.id.name + " reached in evaluation.")
            case other =>
              // Callee's fault
              registerFailed(tfd.fd, evArgs)
              throw EvalError(typeErrorMsg(other, BooleanType))
          }
        case None => 
      }

      callResult

    case other =>
      try {
        super.e(other)
      } catch {
        case t : Throwable =>
          rctx.lastFI foreach registerFailed
          throw t
      }
  }
    
}
