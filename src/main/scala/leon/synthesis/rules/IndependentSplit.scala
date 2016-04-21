/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Types._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Common._

/** Split output if parts of it are independent in the spec.
  * Works in 2 phases:
  * 1) Detuples output variables if they are tuples or case classes to their fields.
  * 2) Tries to split spec in independent parts and solve them separately.
  */
case object IndependentSplit extends NormalizingRule("IndependentSplit") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    /**** Phase 1 ****/
    def isDecomposable(id: Identifier) = id.getType match {
      case CaseClassType(_, _) => true
      case TupleType(_) => true
      case _ => false
    }

    val (newP, recon) = if (p.xs.exists(isDecomposable)) {
      var newPhi = p.phi

      val (subOuts, outerOuts) = p.xs.map { x =>
        x.getType match {
          case ct: CaseClassType =>
            val newIds = ct.fields.map { vd => FreshIdentifier(vd.id.name, vd.getType, true) }

            val newCC = CaseClass(ct, newIds.map(Variable))

            newPhi = subst(x -> newCC, newPhi)

            (newIds, newCC)
          case tt: TupleType =>
            val newIds = tt.bases.zipWithIndex.map{ case (t, ind) =>
              FreshIdentifier(s"${x}_${ind+1}", t, true)
            }
            val newTuple = Tuple(newIds map Variable)
            newPhi = subst(x -> newTuple, newPhi)
            (newIds, newTuple)
          case _ =>
            (List(x), Variable(x))
        }
      }.unzip

      val newOuts = subOuts.flatten

      val newEb = p.qeb.eb.flatMapOuts{ xs => List( (xs zip p.xs) flatMap {
        case (CaseClass(_, args), id) if isDecomposable(id) => args.toList
        case (Tuple(args), _) => args.toList
        case (other, _) => List(other)
      })}

      val newProb = Problem(p.as, p.ws, p.pc, newPhi, newOuts, newEb)
      (newProb, letTuple(newOuts, _:Expr, tupleWrap(outerOuts)))
      //, s"Detuple out ${p.xs.filter(isDecomposable).mkString(", ")}"))
    } else {
      (p, (e: Expr) => e)
    }

    /**** Phase 2 ****/

    val TopLevelAnds(clauses) = andJoin(newP.pc.conditions :+ newP.phi)

    var independentClasses = Set[Set[Identifier]]()

    // We group connect variables together
    for (c <- clauses) {
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

    val outClasses = independentClasses.map(cl => cl & newP.xs.toSet).filter(_.nonEmpty)

    if (outClasses.size > 1) {

      val TopLevelAnds(phiClauses) = newP.phi

      val subs = (for (cl <- outClasses.toList) yield {
        val xs = newP.xs.filter(cl)

        if (xs.nonEmpty) {
          val phi = andJoin(phiClauses.filter(c => (variablesOf(c) & cl).nonEmpty))

          val xsToRemove = newP.xs.filterNot(cl).toSet

          val eb = newP.qeb.removeOuts(xsToRemove)

          Some(newP.copy(phi = phi, xs = xs, eb = eb))
        } else {
          None
        }
      }).flatten

      val onSuccess: List[Solution] => Option[Solution] = { sols =>

        val infos = subs.map(_.xs).zip(sols.map(_.term))

        val term = infos.foldLeft(tupleWrap(newP.xs.map(_.toVariable))) {
          case (expr, (xs, term)) =>
            letTuple(xs, term, expr)
        }

        Some(Solution(andJoin(sols.map(_.pre)), sols.flatMap(_.defs).toSet, recon(term), sols.forall(_.isTrusted)))
      }

      List(decomp(subs, onSuccess, "Independent Clusters"))
    } else {
      Nil
    }
  }
}
