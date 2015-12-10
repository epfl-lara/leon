/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.purescala.Common.Identifier
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Constructors._
import purescala.Types._

import solvers._

import scala.concurrent.duration._

case object InputSplit extends Rule("In. Split") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    p.as.filter(_.getType == BooleanType).flatMap { a =>
        def getProblem(v: Boolean): Problem = {
          def replaceA(e: Expr) = replaceFromIDs(Map(a -> BooleanLiteral(v)), e)

          p.copy(
            as  = p.as.filterNot(_ == a),
            ws  = replaceA(p.ws),
            pc  = replaceA(p.pc),
            phi = replaceA(p.phi),
            eb  = p.qeb.removeIns(Set(a))
          )
        }

        val sub1 = getProblem(true)
        val sub2 = getProblem(false)

        val onSuccess: List[Solution] => Option[Solution] = {
          case List(s1, s2) =>
            Some(Solution(or(and(Equals(Variable(a), BooleanLiteral(true)), s1.pre), 
                             and(Equals(Variable(a), BooleanLiteral(false)), s2.pre)),
                          s1.defs ++ s2.defs, 
                          IfExpr(Variable(a), s1.term, s2.term), s1.isTrusted && s2.isTrusted))
          case _ =>
            None
        }

      Some(decomp(List(sub1, sub2), onSuccess, s"Split on '$a'"))
    }
  }
}
