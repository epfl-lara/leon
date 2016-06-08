package leon.comparison

import leon.comparison.Utils._
import leon.purescala.Expressions.{CaseClassPattern, _}

/**
  * Created by joachimmuth on 25.04.16.
  *
  * This way of basic comparison flat both functional trees into lists and compare them in every possible combination.
  *
  * The easy-to-understand way of working provides a point of comparison for further advanced method.
  *
  * For clarity, we always pass "corpus function" first in argument
  */
object ComparatorByExprList extends Comparator {
  val name = "ExprList"

  def compare(expr_corpus: Expr, expr: Expr)= {
    val exprsA = collectExpr(expr_corpus)
    val exprsB = collectExpr(expr)

    val numberOfSimilarExpr: Int = pairsOfSimilarExp(exprsA, exprsB)

    val score = Utils.matchScore(numberOfSimilarExpr, exprsA.size, exprsB.size)

    if (score > 0.0 && ComparisonPhase.debug){
      println("---------------------")
      println("COMPARATOR " + name)
      println("Expressions: ", expr_corpus, expr)
      println("similar expr: ", numberOfSimilarExpr)
      println("---------------------")
    }

    (score, "")
  }


  def pairsOfSimilarExp(exprs_corpus: List[Expr], exprs: List[Expr]): Int = {
    def helper(exprs_corpus: List[Expr], exprs: List[Expr], acc: Int): Int = exprs match {
      case Nil => acc
      case x::xs if exprs_corpus.contains(x) => helper(exprs_corpus diff List(x), xs, acc + 1)
      case x::xs => helper(exprs_corpus, xs, acc)
    }

    val normalizedExprsA = exprs_corpus.map(normalizeStructure(_))
    val normalizedExprsB = exprs.map(normalizeStructure(_))
    helper(normalizedExprsA, normalizedExprsB, 0)
  }


  /**
    * TO BE DELETED ???
    * --> used in ScoreTree method ???
    *
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
    val expr_base_norm = normalizeStructure(expr_base)
    val expr_norm = normalizeStructure(expr)

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
