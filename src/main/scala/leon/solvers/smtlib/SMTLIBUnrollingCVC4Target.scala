/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import purescala.Definitions.TypedFunDef
import purescala.DefOps.typedTransitiveCallees
import purescala.ExprOps.matchToIfThenElse
import smtlib.parser.Commands._
import smtlib.parser.Terms._

trait SMTLIBUnrollingCVC4Target extends SMTLIBCVC4Target {
  this: SMTLIBSolver =>

  private val typedFunDefExplorationLimit = 10000

  override def targetName = "2.5-cvc4"
  override def declareFunction(tfd: TypedFunDef): SSymbol = {
    if (tfd.params.isEmpty) {
      super[SMTLIBCVC4Target].declareFunction(tfd)
    } else {
      val (funs, exploredAll) = typedTransitiveCallees(Set(tfd), Some(typedFunDefExplorationLimit))
      if (!exploredAll) {
        reporter.warning(
          s"Did not manage to explore the space of typed functions called from ${tfd.id}. The solver may fail"
        )
      }

      val (smtFunDecls, smtBodies) = funs.toSeq.collect {
        case tfd if !functions.containsA(tfd) && tfd.params.nonEmpty =>
          val id = if (tfd.tps.isEmpty) {
            tfd.id
          } else {
            tfd.id.freshen
          }
          val sym = id2sym(id)
          functions +=(tfd, sym)
          (
            FunDec(
              sym,
              tfd.params map { p => SortedVar(id2sym(p.id), declareSort(p.getType)) },
              declareSort(tfd.returnType)
            ),
            toSMT(matchToIfThenElse(tfd.body.get))(tfd.params.map { p =>
              (p.id, id2sym(p.id): Term)
            }.toMap)
            )
      }.unzip

      if (smtFunDecls.nonEmpty) sendCommand(DefineFunsRec(smtFunDecls, smtBodies))
      functions.toB(tfd)
    }
  }

}
