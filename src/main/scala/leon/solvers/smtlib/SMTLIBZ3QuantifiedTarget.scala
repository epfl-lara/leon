package leon.solvers.smtlib

import leon.purescala.DefOps._
import leon.purescala.Definitions.TypedFunDef
import leon.purescala.ExprOps._
import leon.purescala.Expressions.{Equals, FunctionInvocation}
import smtlib.parser.Commands.{DeclareFun, Assert}
import smtlib.parser.Terms.{Term, SortedVar, SSymbol, ForAll}

/**
 * This solver models function definitions as universally quantified formulas.
 * It is not meant as an underlying solver to UnrollingSolver.
 */
trait SMTLIBZ3QuantifiedTarget extends SMTLIBZ3Target {

  this: SMTLIBSolver =>

  private val typedFunDefExplorationLimit = 10000

  override def targetName = "z3-quantified"

  override def declareFunction(tfd: TypedFunDef): SSymbol = {
    if (tfd.params.isEmpty) {
      super[SMTLIBZ3Target].declareFunction(tfd)
    } else {
      val (funs, exploredAll) = typedTransitiveCallees(Set(tfd), Some(typedFunDefExplorationLimit))
      if (!exploredAll) {
        reporter.warning(
          s"Did not manage to explore the space of typed functions called from ${tfd.id}. The solver may fail"
        )
      }

      val smtFunDecls = funs.toSeq.collect {
        case tfd if !functions.containsA(tfd) && tfd.params.nonEmpty =>
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
        val sortedVars = tfd.params.map { p =>
          SortedVar(id2sym(p.id), declareSort(p.getType))
        }
        val term =
          if (sortedVars.isEmpty) {
            toSMT(Equals(FunctionInvocation(tfd, Seq()), tfd.body.get))(Map())
          } else {
            ForAll(
              sortedVars.head,
              sortedVars.tail,
              toSMT(Equals(
                FunctionInvocation(tfd, tfd.params.map {_.toVariable}),
                matchToIfThenElse(tfd.body.get)
              ))(
                tfd.params.map { p => (p.id, id2sym(p.id): Term) }.toMap
              )
            )
        }
        sendCommand(Assert(term))
      }

      functions.toB(tfd)
    }
  }

}
