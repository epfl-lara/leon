/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import purescala.Common.FreshIdentifier
import leon.purescala.Expressions._
import purescala.Definitions.TypedFunDef
import purescala.Constructors.{application, implies}
import purescala.DefOps.typedTransitiveCallees
import smtlib.parser.Commands.Assert
import smtlib.parser.Commands._
import smtlib.parser.Terms._
import smtlib.theories.Core.Equals

trait SMTLIBCVC4QuantifiedTarget extends SMTLIBCVC4Target {
  this: SMTLIBSolver =>

  override val targetName = "cvc4-quantified"

  private val typedFunDefExplorationLimit = 10000

  override def declareFunction(tfd: TypedFunDef): SSymbol = {
    val (funs, exploredAll) = typedTransitiveCallees(Set(tfd), Some(typedFunDefExplorationLimit))
    if (!exploredAll) {
      reporter.warning(
        s"Did not manage to explore the space of typed functions trasitively called from ${tfd.id}. The solver may fail"
      )
    }

    // define-funs-rec does not accept parameterless functions, so we have to treat them differently:
    // we declare-fun each one and assert it is equal to its body
    val (withParams, withoutParams) = funs.toSeq partition( _.params.nonEmpty)

    val parameterlessAssertions = withoutParams filterNot functions.containsA flatMap { tfd =>
      // FIXME: Here we actually want to call super[SMTLIBCVC4Target].declareFunction(tfd),
      // but we inline it to work around a freakish compiler bug
      val id = if (tfd.tps.isEmpty) {
        tfd.id
      } else {
        FreshIdentifier(tfd.id.name)
      }
      sendCommand(DeclareFun(id2sym(id), Seq(), declareSort(tfd.returnType)))
      // Until here, that is.

      functions +=(tfd, id2sym(id))

      try {
        val bodyAssert = Assert(Equals(id2sym(id): Term, toSMT(tfd.body.get)(Map())))

        val specAssert = tfd.postcondition map { post =>
          val term = implies(
            tfd.precondition getOrElse BooleanLiteral(true),
            application(post, Seq(FunctionInvocation(tfd, Seq())))
          )
          Assert(toSMT(term)(Map()))
        }

        Seq(bodyAssert) ++ specAssert
      } catch {
        case _ : IllegalArgumentException =>
          addError()
          Seq()
      }
    }

    val seen = withParams filterNot functions.containsA

    val smtFunDecls = seen map { tfd =>
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

    val smtBodies = smtFunDecls map { case FunDec(sym, _, _) =>
      val tfd = functions.toA(sym)
      try {
        toSMT(tfd.body.get)(tfd.params.map { p =>
          (p.id, id2sym(p.id): Term)
        }.toMap)
      } catch {
        case i: IllegalArgumentException =>
          addError()
          toSMT(Error(tfd.body.get.getType, ""))(Map())
      }
    }

    if (smtFunDecls.nonEmpty) {
      sendCommand(DefineFunsRec(smtFunDecls, smtBodies))
      // Assert contracts for defined functions
      for {
        tfd <- seen
        post <- tfd.postcondition
      } {
        val term = implies(
          tfd.precondition getOrElse BooleanLiteral(true),
          application(post, Seq(FunctionInvocation(tfd, tfd.params map { _.toVariable})))
        )
        sendCommand(Assert(quantifiedTerm(ForAll, term)))
      }
    }

    parameterlessAssertions foreach sendCommand

    functions.toB(tfd)

  }

  // For this solver, we prefer the variables of assert() commands to be exist. quantified instead of free
  override def assertCnstr(expr: Expr) =
    sendCommand(Assert(quantifiedTerm(Exists, expr)))

}
