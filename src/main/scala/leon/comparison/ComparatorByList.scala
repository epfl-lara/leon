package leon.comparison

import leon.purescala.ExprOps
import leon.purescala.Expressions.{CaseClassPattern, _}

/**
  * Created by joachimmuth on 25.04.16.
  *
  * A first attempt and easy to understand comparator.
  * Flat both function into list of argument and compare each of them one-by-one, the similarity result beeing the
  * number of equals-expression divided by its total
  *
  */
object ComparatorByList {
  val print = false

  /**
    * Compare two functions using different method
    *
    * @param expr_base
    * @param expr
    * @return
    */
  def compare(expr_base: Expr, expr: Expr): Double = {
    if (print){
      println("--------------")
      println("COMPARE EXPR")
      println("--------------")
      println("original base expression : ")
      println(expr_base)
      println("original expression : ")
      println(expr)
    }

    val listExpr_base = treeToList(expr_base)
    val listExpr = treeToList(expr)

    if (print){
      println("list base expr")
      println(listExpr_base.size, listExpr_base)
      println("list expr")
      println(listExpr.size, listExpr)
    }

    val similarExprList = for{
      expr_base <- listExpr_base
      expr <- listExpr
      if (compareExpr(expr_base, expr))
    } yield {
      (expr_base, expr)
    }


    if (print)  {
      println("similar Expr List")
      println(similarExprList)
    }

    val percentageSimilarity =
      math.min((similarExprList.size.toDouble / listExpr_base.size.toDouble),
        (similarExprList.size.toDouble / listExpr.size.toDouble)
      )

    percentageSimilarity
  }

  /**
    * Flat an Expression tree into a list in order to provide simple comparison
    *
    * @param expr
    * @return
    */
  def treeToList(expr: Expr): List[Expr] = {
    val list: List[Expr] = expr match {
      case Let(binder, value, body) => List(expr) ++ treeToList(body)

      // we don't list the scrutinee. Why? Because as it will be normalized later, a unique identifier
      // will ALWAYS be the same.
      case MatchExpr(scrutinee, cases) =>
        List (expr)  ++ cases.flatMap(m => m.expressions.flatMap(e => treeToList(e)))

      //default value for any non-handled expression
      case x if x.isInstanceOf[Expr] => List(x)

      //default value for error handling, should never reach that
      case _ => Nil
    }

    list
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
        Utils.compareClass(ct.classDef, ct.classDef)
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

    (expr_base_norm, expr_norm) match {
      case (MatchExpr(_, cases_base), MatchExpr(_, cases)) =>
        val map_case_base = extractPatternMatchMap(cases_base)
        val map_case = extractPatternMatchMap(cases)
        map_case_base == map_case

      case _ =>
        expr_base_norm == expr_norm
    }
  }

}
