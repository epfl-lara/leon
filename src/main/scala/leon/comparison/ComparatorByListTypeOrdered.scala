package leon.comparison

import leon.purescala.Expressions._
import leon.comparison.Utils._

/**
  * Created by joachimmuth on 05.05.16.
  *
  * In contrary of the comparator by List of Expressions, in which each Expr contains its whole tree of children,
  * when we compare type of Expressions between them, we loose the information about children.
  *
  * This is a variation of ComparatorByListType where we check what is the longest sequence of same type.
  *
  */
object ComparatorByListTypeOrdered {
  val name: String = "byListTypeOrdered"

  def compare(expr_base: Expr, expr: Expr): Double = {
    val similarTypeTree: Int = biggestSimilarTypeTree(expr_base, expr)


    val listClassesB = collectClass(expr_base)
    val listClasses = collectClass(expr)

    percentBetweenTwo(similarTypeTree, listClassesB.size, listClasses.size)
  }


  def biggestSimilarTypeTree(expr_base: Expr, expr: Expr): Int = {
    def similarTypeTree(exprB: Expr, expr: Expr, acc: Int) = 0
  0
  }


}
