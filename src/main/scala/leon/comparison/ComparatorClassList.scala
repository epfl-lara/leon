package leon.comparison

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
object ComparatorClassList extends Comparator {
  val name = "ClassList"

  def compare(expr_corpus: Expr, expr: Expr) = {
    val listClassesA = collectClass(expr_corpus)
    val listClassesB = collectClass(expr)

    val similarExpr: Int = pairsOfSimilarExp(listClassesA, listClassesB)

    val score = Utils.matchScore(similarExpr, listClassesA.size, listClassesB.size)

    if (score > 0.0 && ComparisonPhase.debug){
      println("-----------")
      println("COMPARATOR " + name)
      println("Expressions: ", expr, expr_corpus)
      println("List of classes: ", listClassesB, listClassesA)
      println("-----------")
    }

    (score, "")
  }


  def pairsOfSimilarExp(listExpr_corpus: List[Class[_ <: Expr]], listExpr: List[Class[_ <: Expr]]): Int = {
    def helper(listExpr_corpus: List[Class[_ <: Expr]], listExpr: List[Class[_ <: Expr]], acc: Int): Int =
      listExpr match {
        case Nil => acc
        case x::xs if listExpr_corpus.contains(x) => helper(listExpr_corpus diff List(x), xs, acc + 1)
        case x::xs => helper(listExpr_corpus, xs, acc)
      }

    helper(listExpr_corpus, listExpr, 0)
  }

}
