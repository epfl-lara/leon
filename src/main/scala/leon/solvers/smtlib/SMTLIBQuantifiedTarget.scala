/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Expressions._
import purescala.Definitions._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.DefOps.typedTransitiveCallees

import _root_.smtlib.parser.Commands.{Assert => SMTAssert, FunDef => _, _}
import _root_.smtlib.parser.Terms.{Exists => SMTExists, Forall => SMTForall, _ }
import _root_.smtlib.theories.Core.Equals

trait SMTLIBQuantifiedTarget extends SMTLIBTarget {

  protected var currentFunDef: Option[FunDef] = None

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
}
