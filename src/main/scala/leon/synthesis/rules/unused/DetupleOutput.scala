/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules.unused

import purescala.Expressions._
import purescala.Common._
import purescala.Types._
import purescala.Constructors._

case object DetupleOutput extends Rule("Detuple Out") {

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    def isDecomposable(id: Identifier) = id.getType match {
      case CaseClassType(t, _) if !t.isAbstract => true
      case _ => false
    }

    if (p.xs.exists(isDecomposable)) {
      var subProblem = p.phi

      val (subOuts, outerOuts) = p.xs.map { x =>
        if (isDecomposable(x)) {
          val ct = x.getType.asInstanceOf[CaseClassType]

          val newIds = ct.fields.map{ vd => FreshIdentifier(vd.id.name, vd.getType, true) }

          val newCC = CaseClass(ct, newIds.map(Variable))

          subProblem = subst(x -> newCC, subProblem)

          (newIds, newCC)
        } else {
          (List(x), Variable(x))
        }
      }.unzip

      val newOuts = subOuts.flatten

      val sub = Problem(p.as, p.ws, p.pc, subProblem, newOuts)

      val onSuccess: List[Solution] => Option[Solution] = {
        case List(sol) =>
          Some(Solution(sol.pre, sol.defs, letTuple(newOuts, sol.term, tupleWrap(outerOuts)), sol.isTrusted))
        case _ =>
          None
      }

      Some(decomp(List(sub), onSuccess, s"Detuple out ${p.xs.filter(isDecomposable).mkString(", ")}"))
    } else {
      None
    }

  }
}
