/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import purescala._
import Expressions._
import Definitions._
import Constructors._
import DefOps.typedTransitiveCallees
import smtlib.parser.Commands.{Assert => SMTAssert, FunDef => _, _}
import smtlib.parser.Terms.{Exists => SMTExists, ForAll => SMTForall, _ }
import smtlib.theories.Core.Equals

// This solver utilizes the define-funs-rec command of SMTLIB-2.5 to define mutually recursive functions.
// It is not meant as an underlying solver to UnrollingSolver, and does not handle HOFs.
abstract class SMTLIBCVC4QuantifiedSolver(context: LeonContext, program: Program)
  extends SMTLIBCVC4Solver(context, program)
  with SMTLIBQuantifiedSolver
{

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
        val bodyAssert = SMTAssert(Equals(s: Term, toSMT(tfd.body.get)(Map())))

        val specAssert = tfd.postcondition map { post =>
          val term = implies(
            tfd.precondition getOrElse BooleanLiteral(true),
            application(post, Seq(FunctionInvocation(tfd, Seq())))
          )
          SMTAssert(toSMT(term)(Map()))
        }

        Seq(bodyAssert) ++ specAssert
      } catch {
        case _ : IllegalArgumentException =>
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
        case _: IllegalArgumentException =>
          addError()
          toSMT(Error(tfd.body.get.getType, ""))(Map())
      }
    }

    if (smtFunDecls.nonEmpty) {
      sendCommand(DefineFunsRec(smtFunDecls, smtBodies))
      // Assert contracts for defined functions
      if (allowQuantifiedAssersions) for {
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
          sendCommand(SMTAssert(quantifiedTerm(SMTForall, term)))
        } catch {
          case _ : IllegalArgumentException =>
            addError()
        }
      }
    }

    parameterlessAssertions.foreach(a => sendCommand(a))

    functions.toB(tfd)
  }

}
