/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import leon.purescala.ExprOps.CollectorWithPaths
import purescala._
import Expressions._
import ExprOps._
import Definitions._
import Constructors._
import DefOps.typedTransitiveCallees
import leon.verification.{VCKinds, VC}
import smtlib.parser.Commands.{Assert => SMTAssert, FunDef => _, _}
import smtlib.parser.Terms.{Exists => SMTExists, ForAll => SMTForall, _ }
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
        //currentFunDef foreach { f => println(s"${tfd.id.uniqueName} does not refer to ${f.id.uniqueName}") }
        val term = implies(
          tfd.precondition getOrElse BooleanLiteral(true),
          application(post, Seq(FunctionInvocation(tfd, tfd.params map { _.toVariable})))
        )
        try {
          sendCommand(SMTAssert(quantifiedTerm(SMTForall, term)))
        } catch {
          case _ : IllegalArgumentException =>
            addError()
        }
      }
    }

    parameterlessAssertions foreach sendCommand

    functions.toB(tfd)

  }

  // Generates inductive hypotheses for
  protected def generateInductiveHyp: Expr = {
    def collectWithPC[T](f: PartialFunction[Expr, T])(expr: Expr): Seq[(T, Expr)] = {
      CollectorWithPaths(f).traverse(expr)
    }

    //println("Current is" + currentFunDef.get)

    val calls = /*collectWithPC {
      case f : FunctionInvocation => f
    }*/functionCallsOf(currentFunDef.get.body.get) //FIXME too many .get

    //println(calls mkString "\n")

    val inductiveHyps = for {
      fi@FunctionInvocation(tfd, args) <- calls.toSeq
    } yield {
      val post = tfd.postcondition map {
        post => application(replaceFromIDs(tfd.params.map{ _.id}.zip(args).toMap, post), Seq(fi))
      } getOrElse BooleanLiteral(true)
      val pre = tfd.precondition getOrElse BooleanLiteral(true)
      /*implies(pc, */ and(pre, post) //)
    }

    andJoin(inductiveHyps)
  }

  protected def withInductiveHyp(vc: VC): Expr = {
    if (vc.kind == VCKinds.Postcondition) {
      // We want to check if the negation of the vc is sat under inductive hyp.
      // So we need to see if (indHyp /\ !vc) is satisfiable
      liftLets(matchToIfThenElse(and(generateInductiveHyp, not(vc.condition))))
    } else {
      not(vc.condition)
    }
  }

  // We need to know the function context.
  // The reason is we do not want to assume postconditions of functions referring to 
  // the current function, as this may make the proof unsound
  override def assertVC(vc: VC) = {
    currentFunDef = Some(vc.fd)
    assertCnstr(withInductiveHyp(vc))
  }

}
