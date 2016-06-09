package leon.comparison

import leon.purescala.Expressions.Expr

/**
  * Created by joachimmuth on 09.06.16.
  */
trait Scorer {
  def computeScore(exprA: Expr, exprB: Expr): Double

}
