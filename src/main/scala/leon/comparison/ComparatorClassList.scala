package leon.comparison

import leon.{GlobalOptions, LeonContext, utils}
import leon.comparison.Utils._
import leon.purescala.Expressions._

/**
  * Created by joachimmuth on 02.05.16.
  *
  * This method shares similarities with the ComparatorByList.
  * We keep the idea of comparing a list of expressions (disregarding their order), but now, instead of comparing
  * two expressions (i.e. tree) we will extract the type of each expression.
  *
  * x match {
  * case 1 => 'a'
  * case 2 => 'b'
  * }
  *
  * ComparatorByList -> {complete match, leaf(a), leaf(b)}
  * ComparatorByListType -> {node(match), leaf(a), leaf(b)}
  *
  * x match {
  * case 1 => 'a'
  * case 2 => 'c'
  * }
  *
  * ComparatorByList -> similarity 33%
  * ComparatorByListType -> similarity 66%
  */
object ComparatorClassList extends Comparator {
  val name = "ClassList"

  def compare(exprCorpus: Expr, expr: Expr)(implicit context: LeonContext) = {
    implicit val debugSection = utils.DebugSectionComparison
    val listClassesA = collectClass(exprCorpus)
    val listClassesB = collectClass(expr)

    val similarExpr: Int = pairsOfSimilarExp(listClassesA, listClassesB)

    val score = Utils.matchScore(similarExpr, listClassesA.size, listClassesB.size)

    if (context.findOption(GlobalOptions.optDebug).isDefined) {
      context.reporter.debug("-----------")
      context.reporter.debug("COMPARATOR " + name)
      context.reporter.debug("Expressions: \n" + expr + exprCorpus)
      context.reporter.debug("List of classes: \n" + listClassesB + listClassesA)
      context.reporter.debug("-----------")
    }

    (score, "")
  }


  def pairsOfSimilarExp(listExprCorpus: List[Class[_ <: Expr]], listExpr: List[Class[_ <: Expr]]): Int = {
    def helper(listExprCorpus: List[Class[_ <: Expr]], listExpr: List[Class[_ <: Expr]], acc: Int): Int =
      listExpr match {
        case Nil => acc
        case x :: xs if listExprCorpus.contains(x) => helper(listExprCorpus diff List(x), xs, acc + 1)
        case x :: xs => helper(listExprCorpus, xs, acc)
      }

    helper(listExprCorpus, listExpr, 0)
  }

}
