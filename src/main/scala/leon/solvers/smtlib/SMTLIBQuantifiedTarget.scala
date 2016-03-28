/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Expressions._
import purescala.Definitions._
import purescala.Constructors._
import purescala.ExprOps._

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
      fi @ FunctionInvocation(tfd, args) <- functionCallsOf(cond).toSeq
    } yield {
      val post = application(
        tfd.withParamSubst(args, tfd.postOrTrue),
        Seq(fi)
      )
      and(tfd.precOrTrue, post)
    }

    // We want to check if the negation of the vc is sat under inductive hyp.
    // So we need to see if (indHyp /\ !vc) is satisfiable
    liftLets(matchToIfThenElse(andJoin(inductiveHyps :+ not(cond))))
  }
}
