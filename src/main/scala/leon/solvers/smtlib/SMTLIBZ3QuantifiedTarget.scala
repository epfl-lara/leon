/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._
import purescala.Definitions._
import purescala.DefOps.typedTransitiveCallees

import _root_.smtlib.parser.Commands.{Assert => SMTAssert, FunDef => _, _}
import _root_.smtlib.parser.Terms.{Exists => SMTExists, Forall => SMTForall, _ }
import _root_.smtlib.theories.Core.{Equals => SMTEquals}
import _root_.smtlib.parser.Commands._

trait SMTLIBZ3QuantifiedTarget extends SMTLIBZ3Target with SMTLIBQuantifiedTarget {

  protected val allowQuantifiedAssertions: Boolean = true

  override def targetName = "z3-q"

  override def declareFunction(tfd: TypedFunDef): SSymbol = {

    val (funs, exploredAll) = typedTransitiveCallees(Set(tfd), Some(typedFunDefExplorationLimit))

    if (!exploredAll) {
      reporter.warning(
        "Did not manage to explore the space of typed functions " +
          s"transitively called from ${tfd.id}. The solver may fail"
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
      )(Map())
      emit(SMTAssert(term))
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
        emit(SMTAssert(quantifiedTerm(SMTForall, term)(Map())))
      } catch {
        case _ : SMTLIBUnsupportedError =>
          addError()
      }
    }

    functions.toB(tfd)

  }
}
