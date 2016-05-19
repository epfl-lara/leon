package leon.comparison

import leon.purescala.Expressions._
import leon.comparison.Utils._

/**
  * Created by joachimmuth on 02.05.16.
  *
  * This method shares similarities with the ComparatorByList.
  * We kkep the idea of comparing a list of expressions (disregarding their order), but now, instead of comparing
  * two expressions (i.e. tree) we will extract the type of each expression.
  *
  * x match {
  *   case 1 => 'a'
  *   case 2 => 'b'
  * }
  *
  * ComparatorByList -> {complete match, leaf(a), leaf(b)}
  * ComparatorByListType -> {node(match), leaf(a), leaf(b)}
  *
  * x match {
  *   case 1 => 'a'
  *   case 2 => 'c'
  * }
  *
  * ComparatorByList -> similarity 33%
  * ComparatorByListType -> similarity 66%
  */
object ComparatorByClassList extends Comparator {
  val name = "ClassList"

  /**
    * Compare two functions using different method
    *
    * @param expr_base
    * @param expr
    * @return
    */
  def compare(expr_base: Expr, expr: Expr): Double = {
    val listClassesB = collectClass(expr_base)
    val listClasses = collectClass(expr)

    val similarExpr: Int = pairsOfSimilarExp(listClassesB, listClasses)

    val score = Utils.matchScore(similarExpr, listClassesB.size, listClasses.size)

    if (score > 0.0 && ComparisonPhase.debug){
      println("-----------")
      println("COMPARATOR " + name)
      println("Expressions: ", expr, expr_base)
      println("List of classes: ", listClasses, listClassesB)
      println("-----------")
    }

    score
  }


  def pairsOfSimilarExp(listExpr_base: List[Class[_ <: Expr]], listExpr: List[Class[_ <: Expr]]): Int = {
    def helper(listExpr_base: List[Class[_ <: Expr]], listExpr: List[Class[_ <: Expr]], acc: Int): Int =
      listExpr match {
        case Nil => acc
        case x::xs if listExpr_base.contains(x) => helper(listExpr_base diff List(x), xs, acc + 1)
        case x::xs => helper(listExpr_base, xs, acc)
      }

    helper(listExpr_base, listExpr, 0)
  }

}
