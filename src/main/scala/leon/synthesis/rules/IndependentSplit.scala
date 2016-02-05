/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.utils._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Common._
import purescala.Types.CaseClassType

case object IndependentSplit extends NormalizingRule("IndependentSplit") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val TopLevelAnds(clauses) = and(p.pc, p.phi)

    var independentClasses = Set[Set[Identifier]]()

    // We group connect variables together
    for(c <- clauses) {
      val vs = variablesOf(c)

      var newClasses = Set[Set[Identifier]]()

      var thisClass = vs

      for (cl <- independentClasses) {
        if ((cl & vs).nonEmpty) {
          thisClass ++= cl
        } else {
          newClasses += cl
        }
      }

      independentClasses = newClasses + thisClass
    }

    val outClasses = independentClasses.map(cl => cl & p.xs.toSet).filter(_.nonEmpty)

    if (outClasses.size > 1) {

      val TopLevelAnds(phiClauses) = p.phi

      val subs = (for (cl <- outClasses.toList) yield {
        val xs = p.xs.filter(cl)

        if (xs.nonEmpty) {
          val phi = andJoin(phiClauses.filter(c => (variablesOf(c) & cl).nonEmpty))

          val xsToRemove = p.xs.filterNot(cl).toSet

          val eb = p.qeb.removeOuts(xsToRemove)

          Some(p.copy(phi = phi, xs = xs, eb = eb))
        } else {
          None
        }
      }).flatten

      val onSuccess: List[Solution] => Option[Solution] = { sols =>

        val infos = subs.map(_.xs).zip(sols.map(_.term))

        val term = infos.foldLeft(tupleWrap(p.xs.map(_.toVariable))) {
          case (expr, (xs, term)) =>
            letTuple(xs, term, expr)
        }

        Some(Solution(andJoin(sols.map(_.pre)), sols.map(_.defs).flatten.toSet, term, sols.forall(_.isTrusted)))
      }


      List(decomp(subs, onSuccess, "Independent Clusters"))
    } else {
      Nil
    }
  }
}
