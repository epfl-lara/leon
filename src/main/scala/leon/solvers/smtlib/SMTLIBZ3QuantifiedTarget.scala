package leon.solvers.smtlib

import leon.purescala.DefOps._
import leon.purescala.Definitions.TypedFunDef
import leon.purescala.ExprOps._
import leon.purescala.Expressions._
import leon.purescala.Constructors._
import smtlib.parser.Commands.{DeclareFun, Assert}
import smtlib.parser.Terms.{ForAll => SMTForall, SSymbol}

/**
 * This solver models function definitions as universally quantified formulas.
 * It is not meant as an underlying solver to UnrollingSolver.
 */
trait SMTLIBZ3QuantifiedTarget extends SMTLIBZ3Target {

  this: SMTLIBSolver =>

  private val typedFunDefExplorationLimit = 10000

  override def targetName = "z3-quantified"

  override def declareFunction(tfd: TypedFunDef): SSymbol = {

    val (funs, exploredAll) = typedTransitiveCallees(Set(tfd), Some(typedFunDefExplorationLimit))
    if (!exploredAll) {
      reporter.warning(
        s"Did not manage to explore the space of typed functions called from ${tfd.id}. The solver may fail"
      )
    }

    val smtFunDecls = funs.toSeq.collect {
      case tfd if !functions.containsA(tfd) =>
        val id = if (tfd.tps.isEmpty) {
          tfd.id
        } else {
          tfd.id.freshen
        }
        val sym = id2sym(id)
        functions +=(tfd, sym)
        sendCommand(DeclareFun(
          sym,
          tfd.params map { p => declareSort(p.getType) },
          declareSort(tfd.returnType)
        ))
        sym
    }
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
      sendCommand(Assert(term))

      tfd.postcondition foreach { post =>
        val axiom = implies(
          tfd.precondition getOrElse BooleanLiteral(true),
          application(
            post,
            Seq(FunctionInvocation(tfd, tfd.params map { _.toVariable }))
          )
        )
        sendCommand(Assert(quantifiedTerm(SMTForall, axiom)))
      }
    }

    functions.toB(tfd)
  }


}
