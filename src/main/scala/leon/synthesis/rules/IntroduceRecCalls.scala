/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Path
import purescala.Extractors.TopLevelAnds
import purescala.Expressions._
import purescala.Constructors._
import purescala.Common._
import Witnesses.Terminating
import utils.Helpers.terminatingCalls

case object IntroduceRecCalls extends NormalizingRule("Introduce rec. calls") {

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val existingCalls = p.pc.bindings.collect { case (_, fi: FunctionInvocation) => fi }.toSet

    val calls = terminatingCalls(hctx.program, p.ws, p.pc, None, false)
      .map(_._1).distinct.filterNot(existingCalls)

    if (calls.isEmpty) return Nil

    val (recs, paths) = calls.map { newCall =>
      val rec = FreshIdentifier("rec", newCall.getType, alwaysShowUniqueID = true)
      val path = Path.empty withBinding (rec -> newCall)
      (rec, path)
    }.unzip

    val newWs = calls map Terminating
    val TopLevelAnds(ws) = p.ws
    val newProblem = p.copy(
      pc = paths.foldLeft(p.pc)(_ merge _),
      ws = andJoin(ws ++ newWs),
      eb = p.eb
    )

    val onSuccess = forwardMap { e =>
      recs.zip(calls).foldRight(e) {
        case ( (id, call), bd) =>
          Let(id, call, bd)
      }
    }

    List(decomp(List(newProblem), onSuccess, s"Introduce calls ${calls mkString ", "}"))
  }
}
