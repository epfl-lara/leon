package leon
package solvers.smtlib

import purescala._
import DefOps._
import Definitions._
import Expressions._
import Constructors._
import smtlib.parser.Commands.{Assert => SMTAssert}
import smtlib.parser.Terms.{ForAll => SMTForall, SSymbol}

/**
 * This solver models function definitions as universally quantified formulas.
 * It is not meant as an underlying solver to UnrollingSolver, and does not handle HOFs.
 */
class SMTLIBZ3QuantifiedSolver(context: LeonContext, program: Program) extends SMTLIBZ3Solver(context, program) {

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
        super.declareFunction(tfd)
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
      sendCommand(SMTAssert(term))

      tfd.postcondition foreach { post =>
        val axiom = implies(
          tfd.precondition getOrElse BooleanLiteral(true),
          application(
            post,
            Seq(FunctionInvocation(tfd, tfd.params map { _.toVariable }))
          )
        )
        sendCommand(SMTAssert(quantifiedTerm(SMTForall, axiom)))
      }
    }

    functions.toB(tfd)
  }


}
