/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Definitions._
import purescala.Common._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

case object DetupleOutput extends Rule("Detuple Out") {

  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    def isDecomposable(id: Identifier) = id.getType match {
      case CaseClassType(t) if !t.isAbstract => true
      case _ => false
    }

    if (p.xs.exists(isDecomposable)) {
      var subProblem = p.phi

      val (subOuts, outerOuts) = p.xs.map { x =>
        if (isDecomposable(x)) {
          val CaseClassType(ccd @ CaseClassDef(name, _, fields)) = x.getType

          val newIds = fields.map(vd => FreshIdentifier(vd.id.name, true).setType(vd.getType))

          val newCC = CaseClass(ccd, newIds.map(Variable(_)))

          subProblem = subst(x -> newCC, subProblem)

          (newIds, newCC)
        } else {
          (List(x), Variable(x))
        }
      }.unzip

      val newOuts = subOuts.flatten
      //sctx.reporter.warning("newOuts: " + newOuts.toString)

      val sub = Problem(p.as, p.pc, subProblem, newOuts)

      val onSuccess: List[Solution] => Option[Solution] = {
        case List(sol) =>
          Some(Solution(sol.pre, sol.defs, LetTuple(newOuts, sol.term, Tuple(outerOuts))))
        case _ =>
          None
      }


      Some(RuleInstantiation.immediateDecomp(p, this, List(sub), onSuccess, this.name))
    } else {
      Nil
    }
  }
}
