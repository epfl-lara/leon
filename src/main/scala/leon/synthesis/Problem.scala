/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees.TypeTree
import leon.purescala.Common._
import leon.purescala.Constructors._
import leon.purescala.Extractors._

// Defines a synthesis triple of the form:
// ⟦ as ⟨ ws && pc | phi ⟩ xs ⟧
case class Problem(as: List[Identifier], ws: Expr, pc: Expr, phi: Expr, xs: List[Identifier]) {

  override def toString = {
    val pcws = and(ws, pc)
    "⟦ "+as.mkString(";")+", "+(if (pcws != BooleanLiteral(true)) pcws+" ≺ " else "")+" ⟨ "+phi+" ⟩ "+xs.mkString(";")+" ⟧ "
  }

}

object Problem {
  def fromChoose(ch: Choose, pc: Expr = BooleanLiteral(true)): Problem = {
    val xs = ch.vars
    val phi = simplifyLets(ch.pred)
    val as = (variablesOf(And(pc, phi))--xs).toList

    val TopLevelAnds(clauses) = pc

    val (pcs, wss) = clauses.partition {
      case FunctionInvocation(TypedFunDef(fd, _), _) if fd.annotations("witness") => false
      case _ => true
    }

    Problem(as, andJoin(wss), andJoin(pcs), phi, xs)
  }
}
