package leon
package synthesis.stoch

import purescala.Common.Identifier
import purescala.Definitions.Program
import purescala.Expressions.Expr
import purescala.ExprOps
import purescala.Types.TypeTree

object DeBruijnStats {

  type Context = List[(Identifier, TypeTree)]

  def collectAncestors(expr: Expr, ancs: Seq[Seq[List[Expr]]]): Seq[List[Expr]] = {
    if (ancs.isEmpty) Seq(List(expr)) else ancs.map(_.map(_ :+ expr)).flatten
  }

  def collectAncestors(expr: Expr): Seq[List[Expr]] = {
    ExprOps.fold(collectAncestors)(expr)
  }

  def getDeBruijnStats(ctx: LeonContext, p: Program): Seq[List[Expr]] = {
    null
  }

}
