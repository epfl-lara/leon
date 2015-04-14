/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import leon.purescala.Expressions._
import leon.purescala.ExprOps._
import leon.purescala.Types._
import leon.purescala.Common._
import leon.purescala.Constructors._
import leon.purescala.Extractors._
import Witnesses._

// Defines a synthesis triple of the form:
// ⟦ as ⟨ ws && pc | phi ⟩ xs ⟧
case class Problem(as: List[Identifier], ws: Expr, pc: Expr, phi: Expr, xs: List[Identifier]) {

  def inType  = tupleTypeWrap(as.map(_.getType))
  def outType = tupleTypeWrap(xs.map(_.getType))

  override def toString = {
    val pcws = and(ws, pc)
    "⟦ "+as.mkString(";")+", "+(if (pcws != BooleanLiteral(true)) pcws+" ≺ " else "")+" ⟨ "+phi+" ⟩ "+xs.mkString(";")+" ⟧ "
  }

}

object Problem {
  def fromChoose(ch: Choose, pc: Expr = BooleanLiteral(true)): Problem = {
    val xs = {
      val tps = ch.pred.getType.asInstanceOf[FunctionType].from
      tps map (FreshIdentifier("x", _, true))
    }.toList

    val phi = application(simplifyLets(ch.pred), xs map { _.toVariable})
    val as = (variablesOf(And(pc, phi)) -- xs).toList

    // FIXME do we need this at all?
    val TopLevelAnds(clauses) = pc

    // @mk FIXME: Is this needed?
    val (pcs, wss) = clauses.partition {
      case w : Witness => false
      case _ => true
    }

    Problem(as, andJoin(wss), andJoin(pcs), phi, xs)
  }
}
