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
import _root_.smtlib.theories.Core.Equals
import _root_.smtlib.parser.Commands._

trait SMTLIBCVC4QuantifiedTarget extends SMTLIBCVC4Target with SMTLIBQuantifiedTarget {

  override def targetName = "cvc4-quantified"

  override def declareFunction(tfd: TypedFunDef): SSymbol = {
    val (funs, exploredAll) = typedTransitiveCallees(Set(tfd), Some(typedFunDefExplorationLimit))

    if (!exploredAll) {
      reporter.warning(
        "Did not manage to explore the space of typed functions " +
          s"transitively called from ${tfd.id}. The solver may fail"
      )
    }

    // define-funs-rec does not accept parameterless functions, so we have to treat them differently:
    // we declare-fun each one and assert it is equal to its body
    val (withParams, withoutParams) = funs.toSeq filterNot functions.containsA partition(_.params.nonEmpty)

    // FIXME this may introduce dependency errors
    val parameterlessAssertions = withoutParams flatMap { tfd =>
      val s = super.declareFunction(tfd)

      try {
        val bodyAssert = tfd.body.map { body =>
          SMTAssert(Equals(s: Term, toSMT(body)(Map())))
        }

        val specAssert = tfd.postcondition map { post =>
          val term = implies(
            tfd.precondition getOrElse BooleanLiteral(true),
            application(post, Seq(FunctionInvocation(tfd, Seq())))
          )
          SMTAssert(toSMT(term)(Map()))
        }

        bodyAssert ++ specAssert
      } catch {
        case _ : SMTLIBUnsupportedError =>
          addError()
          Seq()
      }
    }

    val smtFunDecls = withParams map { tfd =>
      val id = if (tfd.tps.isEmpty) {
        tfd.id
      } else {
        tfd.id.freshen
      }
      val sym = id2sym(id)
      functions +=(tfd, sym)
      FunDec(
        sym,
        tfd.params map { p => SortedVar(id2sym(p.id), declareSort(p.getType)) },
        declareSort(tfd.returnType)
      )
    }

    val smtBodies = smtFunDecls map { case f =>
      val tfd = functions.toA(f.name)
      try {
        toSMT(tfd.body.get)(tfd.params.map { p =>
          (p.id, id2sym(p.id): Term)
        }.toMap)
      } catch {
        case _: SMTLIBUnsupportedError =>
          addError()
          toSMT(Error(tfd.body.get.getType, ""))(Map())
      }
    }

    if (smtFunDecls.nonEmpty) {
      emit(DefineFunsRec(smtFunDecls, smtBodies))
      // Assert contracts for defined functions
      if (allowQuantifiedAssertions) for {
        // If we encounter a function that does not refer to the current function,
        // it is sound to assume its contracts for all inputs
        tfd <- withParams if !refersToCurrent(tfd.fd)
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
    }

    parameterlessAssertions.foreach(a => emit(a))

    functions.toB(tfd)
  }
}
