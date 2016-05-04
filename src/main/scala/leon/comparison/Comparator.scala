package leon.comparison

import leon.purescala.Expressions.Expr

/**
  * Created by joachimmuth on 04.05.16.
  */
trait Comparator {
  val name: String
  def compare(expr_base: Expr, expr: Expr): Double

}
