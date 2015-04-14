/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Common._
import purescala.Types._
import purescala.ExprOps._
import purescala.Constructors._

case object DetupleInput extends NormalizingRule("Detuple In") {

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    def isDecomposable(id: Identifier) = id.getType match {
      case CaseClassType(t, _) if !t.isAbstract => true
      case TupleType(ts) => true
      case _ => false
    }

    def decompose(id: Identifier): (List[Identifier], Expr, Map[Identifier, Expr]) = id.getType match {
      case cct @ CaseClassType(ccd, _) if !ccd.isAbstract =>
        val newIds = cct.fields.map{ vd => FreshIdentifier(vd.id.name, vd.getType, true) }

        val map = (ccd.fields zip newIds).map{ case (vd, nid) => nid -> CaseClassSelector(cct, Variable(id), vd.id) }.toMap

        (newIds.toList, CaseClass(cct, newIds.map(Variable)), map)

      case TupleType(ts) =>
        val newIds = ts.zipWithIndex.map{ case (t, i) => FreshIdentifier(id.name+"_"+(i+1), t, true) }

        val map = newIds.zipWithIndex.map{ case (nid, i) => nid -> TupleSelect(Variable(id), i+1) }.toMap

        (newIds.toList, tupleWrap(newIds.map(Variable)), map)

      case _ => sys.error("woot")
    }

    if (p.as.exists(isDecomposable)) {
      var subProblem = p.phi
      var subPc      = p.pc
      var subWs      = p.ws

      var reverseMap = Map[Identifier, Expr]()

      val subAs = p.as.map { a =>
        if (isDecomposable(a)) {
          val (newIds, expr, map) = decompose(a)

          subProblem = subst(a -> expr, subProblem)
          subPc      = subst(a -> expr, subPc)
          subWs      = subst(a -> expr, subWs)

          reverseMap ++= map

          newIds
        } else {
          List(a)
        }
      }

      val newAs = subAs.flatten
      //sctx.reporter.warning("newOuts: " + newOuts.toString)

      // Recompose CaseClasses and Tuples.
      // E.g. Cons(l.head, l.tail) ~~> l
      // (t._1, t._2, t._3) ~~> t
      def recompose(e : Expr) : Expr = e match {
        case CaseClass(ct, args) =>
          val (cts, es) = args.zip(ct.fields).map { 
            case (CaseClassSelector(ct, e, id), field) if field.id == id => (ct, e)
            case _ => return e
          }.unzip
          
          if (cts.distinct.size == 1 && es.distinct.size == 1) {
            es.head
          } else {
            e
          }
        case Tuple(args) =>
          val es = args.zipWithIndex.map {
            case (TupleSelect(e, i), index) if i == index + 1 => e
            case _ => return e
          }
          if (es.distinct.size == 1) {
            es.head
          } else {
            e
          }
        case other => other
      }
      
      val sub = Problem(newAs, subWs, subPc, subProblem, p.xs)

      val s = {substAll(reverseMap, _:Expr)} andThen { simplePostTransform(recompose) }
     
      Some(decomp(List(sub), forwardMap(s), s"Detuple ${reverseMap.keySet.mkString(", ")}"))
    } else {
      None
    }
  }
}
