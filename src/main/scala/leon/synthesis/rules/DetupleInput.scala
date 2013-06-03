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

case object DetupleInput extends NormalizingRule("Detuple In") {

  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    def isDecomposable(id: Identifier) = id.getType match {
      case CaseClassType(t) if !t.isAbstract => true
      case TupleType(ts) => true
      case _ => false
    }

    def decompose(id: Identifier): (List[Identifier], Expr, Map[Identifier, Expr]) = id.getType match {
      case CaseClassType(ccd) if !ccd.isAbstract =>
        val CaseClassDef(name, _, fields) = ccd
        val newIds = fields.map(vd => FreshIdentifier(vd.id.name, true).setType(vd.getType))

        val map = (fields zip newIds).map{ case (f, nid) => nid -> CaseClassSelector(ccd, Variable(id), f.id) }.toMap

        (newIds.toList, CaseClass(ccd, newIds.map(Variable(_))), map)

      case TupleType(ts) =>
        val newIds = ts.zipWithIndex.map{ case (t, i) => FreshIdentifier(id.name+"_"+(i+1), true).setType(t) }

        val map = (newIds.zipWithIndex).map{ case (nid, i) => nid -> TupleSelect(Variable(id), i+1) }.toMap

        (newIds.toList, Tuple(newIds.map(Variable(_))), map)

      case _ => sys.error("woot")
    }

    if (p.as.exists(isDecomposable)) {
      var subProblem = p.phi
      var subPc      = p.pc

      var reverseMap = Map[Identifier, Expr]()

      val (subAs, outerAs) = p.as.map { a =>
        if (isDecomposable(a)) {
          val (newIds, expr, map) = decompose(a)

          subProblem = subst(a -> expr, subProblem)
          subPc      = subst(a -> expr, subPc)

          reverseMap ++= map

          (newIds, expr)
        } else {
          (List(a), Variable(a))
        }
      }.unzip

      val newAs = subAs.flatten
      //sctx.reporter.warning("newOuts: " + newOuts.toString)

      val sub = Problem(newAs, subPc, subProblem, p.xs)

      val onSuccess: List[Solution] => Option[Solution] = {
        case List(sol) =>
          val newPre = substAll(reverseMap, sol.pre)
          val newTerm = substAll(reverseMap, sol.term)
          Some(Solution(newPre, sol.defs, newTerm))
        case _ =>
          None
      }


      Some(RuleInstantiation.immediateDecomp(p, this, List(sub), onSuccess, this.name))
    } else {
      Nil
    }
  }
}
