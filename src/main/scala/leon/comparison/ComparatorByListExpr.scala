package leon.comparison

import leon.purescala.ExprOps
import leon.purescala.Expressions.{CaseClassPattern, _}
import leon.comparison.Utils._

/**
  * Created by joachimmuth on 25.04.16.
  *
  * This way of basic comparison flat both functional tree into lists and compare them in every possible combination.
  *
  * The easy-to-understand way of working provide a point of comparison for further advanced method.
  *
  * "foo_base" always represent the item extracted from the base of exemple and is always put in first, in order
  * to avoid confusion
  */
object ComparatorByListExpr extends Comparator {
  val name = "byListExpr"


  /**
    * Compare two functions using different method
    *
    * @param expr_base
    * @param expr
    * @return
    */
  def compare(expr_base: Expr, expr: Expr): Double = {
    val listExpr_base = collectExpr(expr_base)
    val listExpr = collectExpr(expr)

    val numberOfSimilarExpr: Int = pairsOfSimilarExp(listExpr_base, listExpr)

    Utils.percentBetweenTwo(numberOfSimilarExpr, listExpr.size, listExpr_base.size)
  }


  def pairsOfSimilarExp(listExpr_base: List[Expr], listExpr: List[Expr]): Int = {
    def helper(listExpr_base: List[Expr], listExpr: List[Expr], acc: Int): Int = listExpr match {
      case Nil => acc
      case x::xs if listExpr_base.contains(x) => helper(listExpr_base diff List(x), xs, acc + 1)
      case x::xs => helper(listExpr_base, xs, acc)
    }

    val normalizedListExpr_base = listExpr_base.map(ExprOps.normalizeStructure(_)._1)
    val normalizedListExpr = listExpr.map(ExprOps.normalizeStructure(_)._1)
    helper(normalizedListExpr_base, normalizedListExpr, 0)
  }


  /**
    * Extract a map from a PatternMatch function (match...case) in order to be comparable without caring about the
    * order
    * (waring: this comparison make sense only if the MatchCases are exclusives)
    *
    * e.g : list match {
    *   case x::y::xs => foo(x, y) ++ recursion(xs)
    *   case x::xs => Nil
    *   }
    *
    * is not equal to:
    *
    *   list match {
    *   case x::xs => Nil
    *   case x::y::xs => foo(x, y) ++ recursion(xs)
    *   }
    *
    * @param cases_base
    * @return
    */
  def extractPatternMatchMap(cases_base: Seq[MatchCase]) = {
    cases_base.map(a => a.pattern match {
      case InstanceOfPattern(_, ct) => (ct.classDef -> a.rhs)
      case CaseClassPattern(_, ct, _) => {
        println(a)
        (ct.classDef -> a.rhs)
      }
      case _ => (a.pattern -> a.rhs)
    }).toMap
  }


  def extractValueMatchMap(cases_base: Seq[MatchCase]) = {
    cases_base.map(a => a.pattern -> a.rhs).toMap
  }

  // IDEE: comparer les types plutôt que les pattern complet des match case, et éventuellement oublié les optGuard
  def compareExpr(expr_base: Expr, expr: Expr): Boolean = {
    val expr_base_norm = ExprOps.normalizeStructure(expr_base)._1
    val expr_norm = ExprOps.normalizeStructure(expr)._1

//    (expr_base_norm, expr_norm) match {
//      case (MatchExpr(_, cases_base), MatchExpr(_, cases)) =>
//        val map_case_base = extractPatternMatchMap(cases_base)
//        val map_case = extractPatternMatchMap(cases)
//        map_case_base == map_case
//
//      case _ =>
//        expr_base_norm == expr_norm
//
//    }
  expr_base_norm == expr_norm
  }

}
