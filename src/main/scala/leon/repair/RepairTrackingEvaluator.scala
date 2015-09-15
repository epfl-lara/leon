/* Copyright 2009-2015 EPFL, Lausanne */

package leon.repair

import scala.collection.immutable.Map
import scala.collection.mutable.{Map => MMap}
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.Definitions._
import leon.purescala.Quantification._
import leon.LeonContext
import leon.evaluators.RecursiveEvaluator

/** 
 *  This evaluator tracks all dependencies between function calls (.fullCallGraph)
  * as well as if each invocation was successful or erroneous (led to an error)
  * (.fiStatus) 
  */
class RepairTrackingEvaluator(ctx: LeonContext, prog: Program) extends RecursiveEvaluator(ctx, prog, 50000) {
  type RC = CollectingRecContext
  type GC = GlobalContext
  
  def initRC(mappings: Map[Identifier, Expr]) = CollectingRecContext(mappings, None)
  def initGC(model: leon.solvers.Model) = new GlobalContext(model)
  
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
  
  case class CollectingRecContext(mappings: Map[Identifier, Expr], lastFI : Option[FI]) extends RecContext {
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
