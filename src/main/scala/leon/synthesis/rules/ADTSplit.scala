/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import Witnesses._

import purescala.Expressions._
import purescala.Common._
import purescala.Types._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Definitions._
import evaluators.DefaultEvaluator

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

    val candidates = p.allAs.collect {
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
          val isInputVar = p.as.contains(id)
          val cct = CaseClassType(ccd, act.tps)

          val args = cct.fields.map { vd => FreshIdentifier(vd.id.name, vd.getType, true) }.toList

          val whole = CaseClass(cct, args.map(Variable))

          val subPhi = subst(id -> whole, p.phi)
          val subPC = {
            val withSubst = p.pc map (subst(id -> whole, _))
            if (isInputVar) withSubst
            else {
              val mapping = cct.classDef.fields.zip(args).map {
                case (f, a) => a -> caseClassSelector(cct, Variable(id), f.id)
              }
              withSubst.withBindings(mapping).withCond(isInstOf(id.toVariable, cct))
            }
          }
          val subWS = subst(id -> whole, p.ws)

          val eb2 = {
            if (isInputVar) {
              // Filter out examples where id has the wrong type, and fix input variables
              // Note: It is fine to filter here as no evaluation is required
              p.qeb.flatMapIns { inInfo =>
                inInfo.toMap.apply(id) match {
                  case CaseClass(`cct`, vs) =>
                    List(vs ++ inInfo.filter(_._1 != id).map(_._2))
                  case _ =>
                    Nil
                }
              }
            } else {
              p.eb
            }
          }
          val newAs = if (isInputVar) args ::: oas else p.as
          val inactive = (!isInputVar).option(Inactive(id))
          val subProblem = Problem(newAs, subWS, subPC, subPhi, p.xs, eb2).withWs(Seq(Hint(whole)) ++ inactive)
          val subPattern = CaseClassPattern(None, cct, args.map(id => WildcardPattern(Some(id))))

          (cct, subProblem, subPattern)
        }

        val subInfo = subInfo0.sortBy{ case (cct, _, _) =>
          cct.fieldsTypes.count { t => t == act }
        }

        val onSuccess: List[Solution] => Option[Solution] = { sols =>
          val (cases, globalPres) = (for ((sol, (cct, problem, pattern)) <- sols zip subInfo) yield {
            val retrievedArgs = pattern.subPatterns.collect{ case WildcardPattern(Some(id)) => id }
            val substs = (for ((field,arg) <- cct.classDef.fields zip retrievedArgs ) yield {
              (arg, caseClassSelector(cct, id.toVariable, field.id))
            }).toMap
            (
              SimpleCase(pattern, sol.term),
              and(IsInstanceOf(Variable(id), cct), replaceFromIDs(substs, sol.pre))
            )
          }).unzip

          Some(Solution(orJoin(globalPres), sols.flatMap(_.defs).toSet, matchExpr(Variable(id), cases), sols.forall(_.isTrusted)))
        }

        decomp(subInfo.map(_._2).toList, onSuccess, s"ADT Split on '${id.asString}'")
    }
  }
}
