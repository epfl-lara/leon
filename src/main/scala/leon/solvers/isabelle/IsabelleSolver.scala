package leon.solvers.isabelle

import scala.concurrent._
import scala.concurrent.duration._

import scala.math.BigInt

import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.solvers._
import leon.utils.Interruptible
import leon.verification.VC

import edu.tum.cs.isabelle._
import edu.tum.cs.isabelle.api.ProverResult

class IsabelleSolver(val context: LeonContext, program: Program, types: Types, functions: Functions, system: System) extends Solver with Interruptible { self: TimeoutSolver =>

  context.interruptManager.registerForInterrupts(this)

  import system.executionContext

  private def timeout = optTimeout.map(_.millis).getOrElse(Duration.Inf)

  val name = "isabelle"

  private var pending: List[Future[Term]] = Nil
  private var method: Option[String] = None
  private var running: Option[CancellableFuture[_]] = None

  def reset() = { pending = Nil; method = None; running = None }
  private def addPending(future: Future[Term]) = { pending ::= future }
  private def sequencePending() = { Future.sequence(pending) }

  override def assertVC(vc: VC): Unit = {
    val name = vc.fd.qualifiedName(program)
    addPending(functions.term(vc.condition))
    (vc.fd.proofMethod(vc, context), method) match {
      case (None, _) =>
      case (Some(m1), Some(m2)) if m1 == m2 =>
      case (Some(m1), Some(m2)) => context.reporter.error(s"In proof hint for function definition $name: can't override existing method $m2 with method $m1")
      case (Some(m1), None) => method = Some(m1)
    }
  }

  def check: Option[Boolean] = {
    val verdict = sequencePending().flatMapC { ts =>
      Future.traverse(ts)(system.invoke(Pretty)(_).assertSuccess(context)).foreach { strs =>
        context.reporter.debug(s"Attempting to prove disjunction of ${canonicalizeOutput(strs.mkString(", "))}")
      }

      system.cancellableInvoke(Prove)((ts, method))
    }
    running = Some(verdict)

    try {
      Await.result(verdict.future.assertSuccess(context), timeout) match {
        case Some(thm) =>
          context.reporter.debug(s"Proved theorem: ${canonicalizeOutput(thm)}")
          Some(false)
        case None =>
          None
      }
    }
    catch {
      case _: TimeoutException =>
        context.reporter.info("Isabelle timed out")
        verdict.cancel()
        None
      case _: CancellationException =>
        None
    }
  }

  def free(): Unit = {}
  def interrupt(): Unit = { running.foreach(_.cancel()) }
  def recoverInterrupt(): Unit = {}

  def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = None

  // 'check' never returns 'Some(true)'
  def getModel = sys.error("impossible")

  // 'checkAssumptions' never returns 'Some'
  def getUnsatCore = sys.error("impossible")

  // custom 'assertVC'
  def assertCnstr(expression: Expr): Unit = sys.error("impossible")

  // unimplemented
  def pop(): Unit = ???
  def push(): Unit = ???

}
