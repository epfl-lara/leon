/* Copyright 2009-2015 EPFL, Lausanne */

package leon.solvers.smtlib

import leon.purescala.Common.Identifier
import leon.purescala.Constructors._
import leon.purescala.Definitions.FunDef
import leon.purescala.ExprOps._
import leon.purescala.Expressions._
import leon.verification.VC
import smtlib.parser.Terms.{ Term, Forall => SMTForall, _ }

trait SMTLIBQuantifiedSolver extends SMTLIBSolver {

  private var currentFunDef: Option[FunDef] = None
  protected def refersToCurrent(fd: FunDef) = {
    (currentFunDef contains fd) || (currentFunDef exists {
      program.callGraph.transitivelyCalls(fd, _)
    })
  }

  protected val allowQuantifiedAssertions: Boolean

  protected val typedFunDefExplorationLimit = 10000

  protected def withInductiveHyp(cond: Expr): Expr = {

    val inductiveHyps = for {
      fi@FunctionInvocation(tfd, args) <- functionCallsOf(cond).toSeq
    } yield {
      val formalToRealArgs = tfd.params.map{ _.id}.zip(args).toMap
      val post = tfd.postcondition map { post =>
        application(
          replaceFromIDs(formalToRealArgs, post),
          Seq(fi)
        )
      } getOrElse BooleanLiteral(true)
      val pre = tfd.precondition getOrElse BooleanLiteral(true)
      and(pre, post)
    }

    // We want to check if the negation of the vc is sat under inductive hyp.
    // So we need to see if (indHyp /\ !vc) is satisfiable
    liftLets(matchToIfThenElse(andJoin(inductiveHyps :+ not(cond))))

  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = e match {
    case Forall(vs, bd) =>
      quantifiedTerm(SMTForall, vs map { _.id }, bd)
    case _ =>
      super.toSMT(e)(bindings)
  }

  // We need to know the function context.
  // The reason is we do not want to assume postconditions of functions referring to
  // the current function, as this may make the proof unsound
  override def assertVC(vc: VC) = {
    currentFunDef = Some(vc.fd)
    assertCnstr(withInductiveHyp(vc.condition))
  }

  // Normally, UnrollingSolver tracks the input variable, but this one
  // is invoked alone so we have to filter them here
  override def getModel: leon.solvers.Model = {
    val filter = currentFunDef.map{ _.params.map{_.id}.toSet }.getOrElse( (_:Identifier) => true )
    getModel(filter)
  }

}
