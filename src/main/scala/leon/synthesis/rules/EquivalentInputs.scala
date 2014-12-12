/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.utils._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Constructors._

case object EquivalentInputs extends NormalizingRule("EquivalentInputs") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val TopLevelAnds(clauses) = p.pc

    def discoverEquivalences(allClauses: Seq[Expr]): Seq[(Expr, Expr)] = {
      val instanceOfs = allClauses.collect {
        case ccio @ CaseClassInstanceOf(cct, s) => ccio
      }

      var clauses = allClauses.filterNot(instanceOfs.toSet)

      val ccSubsts = for (CaseClassInstanceOf(cct, s) <- instanceOfs) yield {

        val fieldsVals = (for (f <- cct.fields) yield {
          val id = f.id

          clauses.find {
            case Equals(e, CaseClassSelector(`cct`, `s`, `id`)) => true
            case _ => false
          } match {
            case Some(Equals(e, _)) =>
              Some(e)
            case _ =>
              None
          }

        }).flatten

        
        if (fieldsVals.size == cct.fields.size) {
          Some((s, CaseClass(cct, fieldsVals)))
        } else {
          None
        }
      }

      ccSubsts.flatten
    }


    val substs = discoverEquivalences(clauses)

    val postsToInject = substs.collect {
      case (FunctionInvocation(tfd, args), e) if tfd.hasPostcondition =>
        val Some((id, post)) = tfd.postcondition

        replaceFromIDs((tfd.params.map(_.id) zip args).toMap + (id -> e), post)
    }

    if (substs.nonEmpty) {
      val simplifier = Simplifiers.bestEffort(sctx.context, sctx.program) _

      val sub = p.copy(ws = replaceSeq(substs, p.ws), 
                       pc = simplifier(andJoin(replaceSeq(substs, p.pc) +: postsToInject)),
                       phi = simplifier(replaceSeq(substs, p.phi)))

      List(RuleInstantiation.immediateDecomp(p, this, List(sub), forward, this.name))
    } else {
      Nil
    }
  }
}
