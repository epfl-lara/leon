/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import purescala._
import DefOps._
import Definitions._
import Expressions._
import Constructors._
import smtlib.parser.Commands.{Assert => SMTAssert}
import smtlib.parser.Terms.{Forall => SMTForall, SSymbol}

/**
 * This solver models function definitions as universally quantified formulas.
 * It is not meant as an underlying solver to UnrollingSolver, and does not handle HOFs.
 */
class SMTLIBZ3QuantifiedSolver(context: LeonContext, program: Program)
  extends SMTLIBZ3Solver(context, program)
  with SMTLIBQuantifiedSolver
{

  protected val allowQuantifiedAssertions: Boolean = true

  override def targetName = "z3-q"

  override def declareFunction(tfd: TypedFunDef): SSymbol = {

    val (funs, exploredAll) = typedTransitiveCallees(Set(tfd), Some(typedFunDefExplorationLimit))
    if (!exploredAll) {
      reporter.warning(
        s"Did not manage to explore the space of typed functions called from ${tfd.id}. The solver may fail"
      )
    }

    val notSeen = funs.toSeq filterNot functions.containsA

    val smtFunDecls = notSeen map super.declareFunction

    smtFunDecls foreach { sym =>
      val tfd = functions.toA(sym)
      val term = quantifiedTerm(
        SMTForall,
        tfd.params map { _.id },
        Equals(
          FunctionInvocation(tfd, tfd.params.map {_.toVariable}),
          tfd.body.get
        )
      )
      sendCommand(SMTAssert(term))
    }

    // If we encounter a function that does not refer to the current function,
    // it is sound to assume its contracts for all inputs
    if (allowQuantifiedAssertions) for {
      tfd <- notSeen if !refersToCurrent(tfd.fd)
      post <- tfd.postcondition
    } {
      val term = implies(
        tfd.precondition getOrElse BooleanLiteral(true),
        application(post, Seq(tfd.applied))
      )
      try {
        sendCommand(SMTAssert(quantifiedTerm(SMTForall, term)))
      } catch {
        case _ : IllegalArgumentException =>
          addError()
      }
    }

    functions.toB(tfd)

  }

}
