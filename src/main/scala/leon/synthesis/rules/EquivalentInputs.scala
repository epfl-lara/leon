/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.utils._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._

case object EquivalentInputs extends NormalizingRule("EquivalentInputs") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val TopLevelAnds(clauses) = p.pc

    def discoverEquivalences(allClauses: Seq[Expr]): Seq[(Expr, Expr)] = {
      val instanceOfs = allClauses.collect {
        case ccio @ CaseClassInstanceOf(cct, s) => ccio
      }

      val clauses = allClauses.filterNot(instanceOfs.toSet)

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

      // Direct equivalences:
      val directEqs = allClauses.collect {
        case Equals(v1 @ Variable(a1), v2 @ Variable(a2)) if a1 != a2 => (v2, v1)
      }

      ccSubsts.flatten ++ directEqs
    }


    // We could discover one equivalence, which could allow us to discover
    // other equivalences: We do a fixpoint with limit 5.
    val substs = fixpoint({ (substs: Set[(Expr, Expr)]) =>
      val newClauses = substs.map{ case(e,v) => Equals(v, e) } // clauses are directed: foo = obj.f
      substs ++ discoverEquivalences(clauses ++ newClauses)
    }, 5)(Set()).toSeq


    // We are replacing foo(a) with b. We inject postcondition(foo)(a, b).
    val postsToInject = substs.collect {
      case (FunctionInvocation(tfd, args), e) if tfd.hasPostcondition =>
        val Some(post) = tfd.postcondition

        application(replaceFromIDs((tfd.params.map(_.id) zip args).toMap, post), Seq(e))
    }

    if (substs.nonEmpty) {
      val simplifier = Simplifiers.bestEffort(hctx.context, hctx.program) _

      val sub = p.copy(ws = replaceSeq(substs, p.ws), 
                       pc = simplifier(andJoin(replaceSeq(substs, p.pc) +: postsToInject)),
                       phi = simplifier(replaceSeq(substs, p.phi)))

      val subst = replace(
        substs.map{_.swap}.filter{ case (x,y) => formulaSize(x) > formulaSize(y) }.toMap, 
        _:Expr
      )
      
      val substString = substs.map { case (f, t) => f+" -> "+t }

      List(decomp(List(sub), forwardMap(subst), "Equivalent Inputs ("+substString.mkString(", ")+")"))
    } else {
      Nil
    }
  }
}
