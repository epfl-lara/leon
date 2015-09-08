/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import combinators._
import z3._
import smtlib._

import purescala.Definitions._
import scala.reflect.runtime.universe._
import _root_.smtlib.interpreters._

abstract class SolverFactory[+S <: Solver : TypeTag] {
  def getNewSolver(): S

  def shutdown(): Unit = {}

  def reclaim(s: Solver) {
    s.free()
  }

  val name = typeOf[S].toString.split("\\.").last.replaceAll("Solver", "")+"*"
}

object SolverFactory {
  def apply[S <: Solver : TypeTag](builder: () => S): SolverFactory[S] = {
    new SolverFactory[S] {
      def getNewSolver() = builder()
    }
  }

  val definedSolvers = Map(
    "fairz3"         -> "Native Z3 with z3-templates for unfolding (default)",
    "smt-cvc4"       -> "CVC4 through SMT-LIB",
    "smt-z3"         -> "Z3 through SMT-LIB",
    "smt-z3-q"       -> "Z3 through SMT-LIB, with quantified encoding",
    "smt-cvc4-proof" -> "CVC4 through SMT-LIB, in-solver inductive reasoning, for proofs only",
    "smt-cvc4-cex"   -> "CVC4 through SMT-LIB, in-solver finite-model-finding, for counter-examples only",
    "unrollz3"       -> "Native Z3 with leon-templates for unfolding",
    "ground"         -> "Only solves ground verification conditions by evaluating them",
    "enum"           -> "Enumeration-based counter-example-finder",
    "isabelle"       -> "Isabelle2015 through libisabelle with various automated tactics"
  )

  val availableSolversPretty = "Available: " +
    solvers.SolverFactory.definedSolvers.toSeq.sortBy(_._1).map {
      case (name, desc) =>  f"\n  $name%-14s : $desc"
    }.mkString("")

  def getFromSettings(implicit ctx: LeonContext, program: Program): SolverFactory[TimeoutSolver] = {
    val names = ctx.findOptionOrDefault(SharedOptions.optSelectedSolvers)

    if (((names contains "fairz3") || (names contains "unrollz3")) && !hasNativeZ3) {
      if (hasZ3) {
        if (!reported) {
          ctx.reporter.warning("The Z3 native interface is not available, falling back to smt-z3.")
          reported = true
        }
        getFromName(ctx, program)("smt-z3")
      } else if (hasCVC4) {
        if (!reported) {
          ctx.reporter.warning("The Z3 native interface is not available, falling back to smt-cvc4.")
          reported = true
        }
        getFromName(ctx, program)("smt-cvc4")
      } else {
        ctx.reporter.fatalError("No SMT solver available: native Z3 api could not load and 'cvc4' or 'z3' binaries were not found in PATH.")
      }
    } else {
      getFromNames(ctx, program)(names.toSeq : _*)
    }
  }

  private def showSolvers(ctx: LeonContext) = {
    ctx.reporter.error(availableSolversPretty)
    ctx.reporter.fatalError("Aborting Leon...")
  }

  def getFromName(ctx: LeonContext, program: Program)(name: String): SolverFactory[TimeoutSolver] = name match {
    case "fairz3" =>
      SolverFactory(() => new FairZ3Solver(ctx, program) with TimeoutSolver)

    case "unrollz3" =>
      SolverFactory(() => new UnrollingSolver(ctx, program, new UninterpretedZ3Solver(ctx, program)) with TimeoutSolver)

    case "enum"   =>
      SolverFactory(() => new EnumerationSolver(ctx, program) with TimeoutSolver)

    case "ground" =>
      SolverFactory(() => new GroundSolver(ctx, program) with TimeoutSolver)

    case "smt-z3" =>
      SolverFactory(() => new UnrollingSolver(ctx, program, new SMTLIBZ3Solver(ctx, program)) with TimeoutSolver)

    case "smt-z3-q" =>
      SolverFactory(() => new SMTLIBZ3QuantifiedSolver(ctx, program) with TimeoutSolver)

    case "smt-cvc4" =>
      SolverFactory(() => new UnrollingSolver(ctx, program, new SMTLIBCVC4Solver(ctx, program)) with TimeoutSolver)

    case "smt-cvc4-proof" =>
      SolverFactory(() => new SMTLIBCVC4ProofSolver(ctx, program) with TimeoutSolver)

    case "smt-cvc4-cex" =>
      SolverFactory(() => new SMTLIBCVC4CounterExampleSolver(ctx, program) with TimeoutSolver)

    case "isabelle" =>
      new isabelle.IsabelleSolverFactory(ctx, program)

    case _ =>
      ctx.reporter.error(s"Unknown solver $name")
      showSolvers(ctx)
  }

  def getFromNames(ctx: LeonContext, program: Program)(names: String*): SolverFactory[TimeoutSolver] = {

    val selectedSolvers = names.map(getFromName(ctx, program))

    if (selectedSolvers.isEmpty) {
      ctx.reporter.error(s"No solver selected.")
      showSolvers(ctx)
    } else if (selectedSolvers.size == 1) {
      selectedSolvers.head
    } else {
      new PortfolioSolverFactory(ctx, selectedSolvers.toSeq)
    }

  }

  // Solver qualifiers that get used internally:

  private var reported = false

  // Fast solver used by simplifications, to discharge simple tautologies
  def uninterpreted(ctx: LeonContext, program: Program): SolverFactory[TimeoutSolver] = {
    if (hasNativeZ3) {
      SolverFactory(() => new UninterpretedZ3Solver(ctx, program) with TimeoutSolver)
    } else {
      if (!reported) {
        ctx.reporter.warning("The Z3 native interface is not available, falling back to smt-based solver.")
        reported = true
      }
      SolverFactory(() => new SMTLIBZ3Solver(ctx, program) with TimeoutSolver)
    }
  }

  // Full featured solver used by default
  def default(implicit ctx: LeonContext, program: Program): SolverFactory[TimeoutSolver] = {
    getFromName(ctx, program)("fairz3")
  }

  lazy val hasNativeZ3 = {
    try {
      new _root_.z3.scala.Z3Config
      true
    } catch {
      case _: java.lang.UnsatisfiedLinkError =>
        false
    }
  }

  lazy val hasZ3 = try {
    Z3Interpreter.buildDefault
    true
  } catch {
    case e: java.io.IOException =>
      false
  }

  lazy val hasCVC4 = try {
    CVC4Interpreter.buildDefault
    true
  } catch {
    case e: java.io.IOException =>
      false
  }

}
