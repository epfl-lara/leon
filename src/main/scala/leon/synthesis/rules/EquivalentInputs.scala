/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.utils._
import purescala.Path
import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Constructors._
import purescala.Types.CaseClassType

case object EquivalentInputs extends NormalizingRule("EquivalentInputs") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    val simplifier = Simplifiers.bestEffort(hctx, hctx.program)(_:Expr)

    var subst = Map.empty[Identifier, Expr]
    var reverseSubst = Map.empty[Identifier, Expr]

    var obsolete = Set.empty[Identifier]
    var free = Set.empty[Identifier]

    def discoverEquivalences(p: Path): Path = {

      val vars = p.variables
      val clauses = p.conditions

      val instanceOfs = clauses.collect { case IsInstanceOf(Variable(id), cct) if vars(id) => id -> cct }.toSet

      val equivalences = (for ((sid, cct: CaseClassType) <- instanceOfs) yield {
        val fieldVals = for (f <- cct.classDef.fields) yield {
          val fid = f.id

          p.bindings.collectFirst {
            case (id, CaseClassSelector(`cct`, Variable(`sid`), `fid`)) => id
            case (id, CaseClassSelector(`cct`, AsInstanceOf(Variable(`sid`), `cct`), `fid`)) => id
          }
        }

        if (fieldVals.forall(_.isDefined)) {
          Some(sid -> CaseClass(cct, fieldVals.map(_.get.toVariable)))
        } else if (fieldVals.exists(_.isDefined)) {
          Some(sid -> CaseClass(cct, (cct.fields zip fieldVals).map {
            case (_, Some(id)) => Variable(id)
            case (vid, None) => Variable(vid.id.freshen)
          }))
        } else {
          None
        }
      }).flatten

      val unbound = equivalences.flatMap(_._2.args.collect { case Variable(id) => id })
      obsolete ++= equivalences.map(_._1)
      free ++= unbound

      def replace(e: Expr) = simplifier(replaceFromIDs(equivalences.toMap, e))
      subst = subst.mapValues(replace) ++ equivalences

      val reverse = equivalences.toMap.flatMap { case (id, CaseClass(cct, fields)) =>
        (cct.classDef.fields zip fields).map { case (vid, Variable(fieldId)) =>
          fieldId -> caseClassSelector(cct, asInstOf(Variable(id), cct), vid.id)
        }
      }

      reverseSubst ++= reverse.mapValues(replaceFromIDs(reverseSubst, _))

      (p -- unbound) map replace
    }

    // We could discover one equivalence, which could allow us to discover
    // other equivalences: We do a fixpoint with limit 5.
    val newPC = fixpoint({ (path: Path) => discoverEquivalences(path) }, 5)(p.pc)

    if (subst.nonEmpty) {
      // XXX: must take place in this order!! obsolete & free is typically non-empty
      val newAs = (p.as ++ free).distinct.filterNot(obsolete)

      val newBank = p.eb.flatMap { ex =>
        val mapping = (p.as zip ex.ins).toMap
        val newIns = newAs.map(a => mapping.getOrElse(a, replaceFromIDs(mapping, reverseSubst(a))))
        List(ex match {
          case ioe @ InOutExample(ins, outs) => ioe.copy(ins = newIns)
          case ie @ InExample(ins) => ie.copy(ins = newIns)
        })
      }

      val simplifierWithNewPC = Simplifiers.bestEffort(hctx, hctx.program)(_:Expr, newPC)

      val sub = p.copy(
        as = newAs,
        ws = replaceFromIDs(subst, p.ws),
        pc = newPC,
        phi = simplifierWithNewPC(replaceFromIDs(subst, p.phi)),
        eb = newBank
      )

      val onSuccess = {
        val reverse = subst.map(_.swap).mapValues(_.toVariable)
        forwardMap(replace(reverse, _))
      }

      val substString = subst.map { case (f, t) => f.asString+" -> "+t.asString }

      List(decomp(List(sub), onSuccess, "Equivalent Inputs ("+substString.mkString(", ")+")"))
    } else {
      Nil
    }
  }
}
