/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import purescala._
import Expressions._
import Definitions._
import Constructors.{application, implies}
import DefOps.typedTransitiveCallees
import verification.VC
import smtlib.parser.Commands.{Assert => SMTAssert, FunDef => _, _}
import smtlib.parser.Terms._
import smtlib.theories.Core.Equals

// This solver utilizes the define-funs-rec command of SMTLIB-2.5 to define mutually recursive functions.
// It is not meant as an underlying solver to UnrollingSolver, and does not handle HOFs.
abstract class SMTLIBCVC4QuantifiedSolver(context: LeonContext, program: Program) extends SMTLIBCVC4Solver(context, program) {

  override def targetName = "cvc4-quantified"
  
  private var currentFunDef: Option[FunDef] = None
  def refersToCurrent(fd: FunDef) = {
    (currentFunDef contains fd) || (currentFunDef exists {
      program.callGraph.transitivelyCalls(fd, _)
    })
  }

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

    val notSeen = withParams filterNot functions.containsA

    val smtFunDecls = notSeen map { tfd =>
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
      //println("smtFuns: ")
      //println(smtFunDecls map { _.name.name} mkString ", ")
      //println(s"current: ${currentFunDef.get.id}")
      sendCommand(DefineFunsRec(smtFunDecls, smtBodies))
      // Assert contracts for defined functions
      for {
        // Exclude contracts of functions that refer to current to avoid unsoundness
        tfd <- notSeen if !refersToCurrent(tfd.fd)
        post <- tfd.postcondition
      } {
        //println(s"${tfd.id.uniqueName} does not refer to ${currentFunDef.get.id.uniqueName}")
        val term = implies(
          tfd.precondition getOrElse BooleanLiteral(true),
          application(post, Seq(FunctionInvocation(tfd, tfd.params map { _.toVariable})))
        )
        try {
          sendCommand(SMTAssert(quantifiedTerm(ForAll, term)))
        } catch {
          case _ : IllegalArgumentException =>
            addError()
        }
      }
    }

    parameterlessAssertions foreach sendCommand

    functions.toB(tfd)

  }

  // For this solver, we prefer the variables of assert() commands to be exist. quantified instead of free
  override def assertCnstr(expr: Expr) =
    try {
      sendCommand(SMTAssert(quantifiedTerm(Exists, expr)))
    } catch {
      case _ : IllegalArgumentException =>
        addError()
    }

  // We need to know the function context.
  // The reason is we do not want to assume postconditions of functions referring to 
  // the current function, as this may make the proof unsound
  override def assertVC(vc: VC) = {
    currentFunDef = Some(vc.fd)
    super.assertVC(vc)
  }

}
