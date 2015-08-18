/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Definitions._
import purescala.ExprOps._
import purescala.Expressions._
import synthesis.utils.Helpers._

case class SafeRecursiveCalls(prog: Program, ws: Expr, pc: Expr) extends ExpressionGrammar[TypeTree] {
  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Gen] = {
    val calls = terminatingCalls(prog, t, ws, pc)

    calls.map {
      case (e, free) =>
        val freeSeq = free.toSeq

        nonTerminal(freeSeq.map(_.getType), { sub => replaceFromIDs(freeSeq.zip(sub).toMap, e) })
    }
  }
}
