/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Types._
import solvers.sygus._

import grammars._
import utils._

case object Sygus extends Rule("Sygus") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    if (p.xs.size != 1) {
      Nil
    } else {
      List(new RuleInstantiation(this.name) {
        def apply(hctx: SearchContext): RuleApplication = {

          val sctx = hctx.sctx
          val grammar = Grammars.default(sctx, p)

          val s = new CVC4SygusSolver(sctx.context, sctx.program, p)

          s.checkSynth() match {
            case Some(expr) =>
              RuleClosed(Solution.term(expr))
            case None =>
              RuleFailed()
          }
        }
      })
    }
  }
}
