/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import Witnesses.Hint
import purescala.Expressions._
import purescala.Common._
import purescala.Types._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Definitions._

/** Abstract data type split. If a variable is typed as an abstract data type, then
  * it will create a match case statement on all known subtypes. */
case object ADTSplit extends Rule("ADT Split.") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    // We approximate knowledge of types based on facts found at the top-level
    // we don't care if the variables are known to be equal or not, we just
    // don't want to split on two variables for which only one split
    // alternative is viable. This should be much less expensive than making
    //  calls to a solver for each pair.
    val facts: Map[Identifier, CaseClassType] = {
      val TopLevelAnds(as) = andJoin(p.pc.conditions :+ p.phi)
      val instChecks: Seq[(Identifier, CaseClassType)] = as.collect {
        case IsInstanceOf(Variable(a), cct: CaseClassType) => a -> cct
        case Equals(Variable(a), CaseClass(cct, _))        => a -> cct
      }
      val boundCcs = p.pc.bindings.collect { case (id, CaseClass(cct, _)) => id -> cct }
      instChecks.toMap ++ boundCcs
    }

    val candidates = p.as.collect {
      case IsTyped(id, act @ AbstractClassType(cd, tpes)) =>

        val optCases = cd.knownDescendants.sortBy(_.id.name).collect {
          case ccd : CaseClassDef =>
            val cct = CaseClassType(ccd, tpes)

            if (facts contains id) {
              if (cct == facts(id)) {
                Seq(ccd)
              } else {
                Nil
              }
            } else {
              Seq(ccd)
            }
        }

        val cases = optCases.flatten

        if (cases.nonEmpty) {
          Some((id, act, cases))
        } else {
          None
        }
    }

    candidates.collect {
      case Some((id, act, cases)) =>
        val oas = p.as.filter(_ != id)

        val subInfo0 = for(ccd <- cases) yield {
          val cct    = CaseClassType(ccd, act.tps)

          val args   = cct.fields.map { vd => FreshIdentifier(vd.id.name, vd.getType, true) }.toList

          val whole =  CaseClass(cct, args.map(Variable))

          val subPhi = subst(id -> whole, p.phi)
          val subPC  = p.pc map (subst(id -> whole, _))
          val subWS  = subst(id -> whole, p.ws)

          val eb2 = p.qeb.mapIns { inInfo =>
             inInfo.toMap.apply(id) match {
               case CaseClass(`cct`, vs) =>
                 List(vs ++ inInfo.filter(_._1 != id).map(_._2))
               case _ =>
                 Nil
             }
          }

          val subProblem = Problem(args ::: oas, subWS, subPC, subPhi, p.xs, eb2).withWs(Seq(Hint(whole)))
          val subPattern = CaseClassPattern(None, cct, args.map(id => WildcardPattern(Some(id))))

          (cct, subProblem, subPattern)
        }

        val subInfo = subInfo0.sortBy{ case (cct, _, _) =>
          cct.fieldsTypes.count { t => t == act }
        }


        val onSuccess: List[Solution] => Option[Solution] = {
          case sols =>
            var globalPre = List[Expr]()

            val cases = for ((sol, (cct, problem, pattern)) <- sols zip subInfo) yield {
              if (sol.pre != BooleanLiteral(true)) {
                val substs = (for ((field,arg) <- cct.classDef.fields zip problem.as ) yield {
                  (arg, caseClassSelector(cct, id.toVariable, field.id))
                }).toMap
                globalPre ::= and(IsInstanceOf(Variable(id), cct), replaceFromIDs(substs, sol.pre))
              } else {
                globalPre ::= BooleanLiteral(true)
              }

              SimpleCase(pattern, sol.term)
            }

            Some(Solution(orJoin(globalPre), sols.flatMap(_.defs).toSet, matchExpr(Variable(id), cases), sols.forall(_.isTrusted)))
        }

        decomp(subInfo.map(_._2).toList, onSuccess, s"ADT Split on '${id.asString}'")
    }
  }
}
