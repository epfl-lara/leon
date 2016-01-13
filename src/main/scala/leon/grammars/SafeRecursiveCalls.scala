/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Definitions._
import purescala.ExprOps._
import purescala.Expressions._
import synthesis.utils.Helpers._

/** Generates recursive calls that will not trivially result in non-termination.
  *
  * @param ws An expression that contains the known set [[synthesis.Witnesses.Terminating]] expressions
  * @param pc The path condition for the generated [[Expr]] by this grammar
  */
case class SafeRecursiveCalls(prog: Program, ws: Expr, pc: Expr) extends ExpressionGrammar[TypeTree] {
  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Prod] = {
    val calls = terminatingCalls(prog, t, ws, pc)

    calls.map {
      case (fi, free) =>
        val freeSeq = free.toSeq

        nonTerminal(
          freeSeq.map(_.getType),
          { sub => replaceFromIDs(freeSeq.zip(sub).toMap, fi) },
          Tags.tagOf(fi.tfd.fd, isSafe = true)
        )
    }
  }
}
