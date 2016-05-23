/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Path
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
case class SafeRecursiveCalls(prog: Program, ws: Expr, pc: Path) extends SimpleExpressionGrammar {
  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Prod] = {
    val calls = terminatingCalls(prog,ws, pc, Some(t), true)

    calls.map { c => (c: @unchecked) match {
      case (fi, Some(free)) =>
        val freeSeq = free.toSeq

        nonTerminal(
          freeSeq.map(_.getType),
          sub => replaceFromIDs(freeSeq.zip(sub).toMap, fi),
          Tags.tagOf(fi.tfd.fd, isSafe = true),
          formulaSize(fi) - freeSeq.size
        )
    }}
  }
}
