/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import combinators._
import unrolling._
import z3._
import cvc4._
import smtlib._

import purescala.Definitions._
import scala.reflect.runtime.universe._
import _root_.smtlib.interpreters._

abstract class SolverFactory[+S <: Solver] {
  def getNewSolver(): S

  def shutdown(): Unit = {}

  def reclaim(s: Solver) {
    s.free()
  }

  val name: String
}

object SolverFactory {
  def apply[S <: Solver : TypeTag](nme: String, builder: () => S): SolverFactory[S] = {
    new SolverFactory[S] {
      val name = nme
      def getNewSolver() = builder()
    }
  }

  val definedSolvers = Map(
    "fairz3"         -> "Native Z3 with z3-templates for unrolling (default)",
    "smt-cvc4"       -> "CVC4 through SMT-LIB",
    "smt-z3"         -> "Z3 through SMT-LIB",
    "smt-z3-q"       -> "Z3 through SMT-LIB, with quantified encoding",
    "smt-cvc4-proof" -> "CVC4 through SMT-LIB, in-solver inductive reasoning, for proofs only",
    "smt-cvc4-cex"   -> "CVC4 through SMT-LIB, in-solver finite-model-finding, for counter-examples only",
    "unrollz3"       -> "Native Z3 with leon-templates for unrolling",
    "ground"         -> "Only solves ground verification conditions by evaluating them",
    "enum"           -> "Enumeration-based counter-example-finder",
    "isabelle"       -> "Isabelle2015 through libisabelle with various automated tactics"
  )

  val availableSolversPretty = "Available: " +
    solvers.SolverFactory.definedSolvers.toSeq.sortBy(_._1).map {
      case (name, desc) =>  f"\n  $name%-14s : $desc"
    }.mkString("")

  def getFromSettings(implicit ctx: LeonContext, program: Program): SolverFactory[TimeoutSolver] =
    getFromSettings(SolverContext(ctx, new evaluators.EvaluationBank), program)

  def getFromSettings(implicit ctx: SolverContext, program: Program): SolverFactory[TimeoutSolver] = {
    val names = ctx.context.findOptionOrDefault(GlobalOptions.optSelectedSolvers)

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

  private def showSolvers(ctx: SolverContext) = {
    ctx.reporter.error(availableSolversPretty)
    ctx.reporter.fatalError("Aborting Leon...")
  }

  def getFromName(ctx: LeonContext, program: Program)(name: String): SolverFactory[TimeoutSolver] =
    getFromName(SolverContext(ctx, new evaluators.EvaluationBank), program)(name)

  def getFromName(ctx: SolverContext, program: Program)(name: String): SolverFactory[TimeoutSolver] = name match {
    case "enum"           => SolverFactory(name, () => new EnumerationSolver(ctx, program) with TimeoutSolver)
    case "ground"         => SolverFactory(name, () => new GroundSolver(ctx, program) with TimeoutSolver)
    case "fairz3"         => SolverFactory(name, () => new FairZ3Solver(ctx, program) with TimeoutSolver)
    case "unrollz3"       => SolverFactory(name, () => new Z3UnrollingSolver(ctx, program, new UninterpretedZ3Solver(ctx, program)) with TimeoutSolver)
    case "smt-z3"         => SolverFactory(name, () => new Z3UnrollingSolver(ctx, program, new SMTLIBZ3Solver(ctx, program)) with TimeoutSolver)
    case "smt-z3-q"       => SolverFactory(name, () => new SMTLIBZ3QuantifiedSolver(ctx, program) with TimeoutSolver)
    case "smt-cvc4"       => SolverFactory(name, () => new CVC4UnrollingSolver(ctx, program, new SMTLIBCVC4Solver(ctx, program)) with TimeoutSolver)
    case "smt-cvc4-proof" => SolverFactory(name, () => new SMTLIBCVC4ProofSolver(ctx, program) with TimeoutSolver)
    case "smt-cvc4-cex"   => SolverFactory(name, () => new SMTLIBCVC4CounterExampleSolver(ctx, program) with TimeoutSolver)
    case "smt-z3-u"       => SolverFactory(name, () => new SMTLIBZ3Solver(ctx, program) with TimeoutSolver)
    case "smt-cvc4-u"     => SolverFactory(name, () => new SMTLIBCVC4Solver(ctx, program) with TimeoutSolver)
    case "nativez3-u"     => SolverFactory(name, () => new UninterpretedZ3Solver(ctx, program) with TimeoutSolver)
    case "isabelle"       => new isabelle.IsabelleSolverFactory(ctx.context, program)
    case _ =>
      ctx.reporter.error(s"Unknown solver $name")
      showSolvers(ctx)
  }

  def getFromNames(ctx: SolverContext, program: Program)(names: String*): SolverFactory[TimeoutSolver] = {

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
    val names = ctx.findOptionOrDefault(GlobalOptions.optSelectedSolvers)
    val fromName = getFromName(ctx, program) _

    if ((names contains "fairz3") && !hasNativeZ3) {
      if (hasZ3) {
        if (!reported) {
          ctx.reporter.warning("The Z3 native interface is not available, falling back to smt-z3.")
          reported = true
        }
        fromName("smt-z3-u")
      } else if (hasCVC4) {
        if (!reported) {
          ctx.reporter.warning("The Z3 native interface is not available, falling back to smt-cvc4.")
          reported = true
        }
        fromName("smt-cvc4-u")
      } else {
        ctx.reporter.fatalError("No SMT solver available: native Z3 api could not load and 'cvc4' or 'z3' binaries were not found in PATH.")
      }
    } else if(names contains "smt-cvc4") {
      fromName("smt-cvc4-u")
    } else if(names contains "smt-z3") {
      fromName("smt-z3-u")
    } else if ((names contains "fairz3") && hasNativeZ3) {
      fromName("nativez3-u")
    } else {
      ctx.reporter.fatalError("No SMT solver available: native Z3 api could not load and 'cvc4' or 'z3' binaries were not found in PATH.")
    }
  }

  // Full featured solver used by default
  def default(implicit ctx: LeonContext, program: Program): SolverFactory[TimeoutSolver] = {
    getFromName(ctx, program)("fairz3")
  }

  lazy val hasNativeZ3 = try {
    _root_.z3.Z3Wrapper.withinJar()
    true
  } catch {
    case _: java.lang.UnsatisfiedLinkError =>
      false
  }

  lazy val hasZ3 = try {
    new Z3Interpreter("z3", Array("-in", "-smt2"))
    true
  } catch {
    case e: java.io.IOException =>
      false
  }

  lazy val hasCVC4 = try {
    new CVC4Interpreter("cvc4", Array("-q", "--lang", "smt2.5"))
    true
  } catch {
    case e: java.io.IOException =>
      false
  }

}
