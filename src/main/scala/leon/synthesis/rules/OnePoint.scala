/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Constructors._

case object OnePoint extends NormalizingRule("One-point") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val TopLevelAnds(exprs) = p.phi

    def validOnePoint(x: Identifier, e: Expr) = {
      !(variablesOf(e) contains x)
    }

    val candidates = exprs.collect {
      case eq @ Equals(Variable(x), e) if (p.xs contains x) && validOnePoint(x, e) =>
        (x, e, eq)
      case eq @ Equals(e, Variable(x)) if (p.xs contains x) && validOnePoint(x, e) =>
        (x, e, eq)
    }

    if (candidates.nonEmpty) {
      val (x, e, eq) = candidates.head

      val others = exprs.filter(_ != eq)
      val oxs    = p.xs.filter(_ != x)

      val newProblem = Problem(p.as, p.ws, p.pc, subst(x -> e, andJoin(others)), oxs)

      val onSuccess: List[Solution] => Option[Solution] = {
        case List(s @ Solution(pre, defs, term)) =>
          Some(Solution(pre, defs, letTuple(oxs, term, subst(x -> e, tupleWrap(p.xs.map(Variable)))), s.isTrusted))
        case _ =>
          None
      }

      List(decomp(List(newProblem), onSuccess, s"One-point on $x = $e"))
    } else {
      Nil
    }
  }
}

