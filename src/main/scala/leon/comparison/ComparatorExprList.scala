package leon.comparison

import leon.{GlobalOptions, LeonContext}
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
object ComparatorExprList extends Comparator {
  val name = "ExprList"

  def compare(exprCorpus: Expr, expr: Expr)(implicit context: LeonContext) = {
    val exprsA = collectExpr(exprCorpus)
    val exprsB = collectExpr(expr)

    val numberOfSimilarExpr: Int = pairsOfSimilarExp(exprsA, exprsB)

    val score = Utils.matchScore(numberOfSimilarExpr, exprsA.size, exprsB.size)

    if (context.findOption(GlobalOptions.optDebug).isDefined){
      println("---------------------")
      println("COMPARATOR " + name)
      println("Expressions: ", exprCorpus, expr)
      println("similar expr: ", numberOfSimilarExpr)
      println("---------------------")
    }

    (score, "")
  }


  def pairsOfSimilarExp(exprsCorpus: List[Expr], exprs: List[Expr]): Int = {
    val normalizedExprsA = exprsCorpus.map(normalizeStructure(_))
    val normalizedExprsB = exprs.map(normalizeStructure(_))

    normalizedExprsA.intersect(normalizedExprsB).size
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
    * @param matchCases
    * @return
    */
  def extractPatternMatchMap(matchCases: Seq[MatchCase]) = {
    matchCases.map(a => a.pattern match {
      case InstanceOfPattern(_, ct) => (ct.classDef -> a.rhs)
      case CaseClassPattern(_, ct, _) => {
        println(a)
        (ct.classDef -> a.rhs)
      }
      case _ => (a.pattern -> a.rhs)
    }).toMap
  }


  def extractValueMatchMap(matchCases: Seq[MatchCase]) = {
    matchCases.map(a => a.pattern -> a.rhs).toMap
  }

  // IDEE: comparer les types plutôt que les pattern complet des match case, et éventuellement oublié les optGuard
  def compareExpr(exprA: Expr, exprB: Expr): Boolean = {
    val normalizedExprA = normalizeStructure(exprA)
    val normalizedExprB = normalizeStructure(exprB)

  normalizedExprA == normalizedExprB
  }

}
