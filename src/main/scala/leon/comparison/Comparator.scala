package leon.comparison

import leon.LeonContext
import leon.purescala.Expressions.Expr

/**
  * Created by joachimmuth on 04.05.16.
  */
trait Comparator {
  val name: String
  def compare(exprCorpus: Expr, expr: Expr)(implicit context: LeonContext): (Double, String)

}
