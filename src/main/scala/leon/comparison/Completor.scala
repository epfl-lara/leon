package leon.comparison

import leon.LeonContext
import leon.purescala.Definitions.FunDef
import leon.purescala.Expressions._
import leon.comparison.Utils._
import leon.comparison.ComparatorDirectScoreTree._
import leon.purescala.ExprOps

/**
  * Created by joachimmuth on 08.06.16.
  *
  * Consider a holed function and try to find the best match (if there is some!) between this and one of the function
  * existing in the corpus.
  *
  * To do so, we use a similar method as ComparatorDirectScoreTree were we create all possible common tree shared by
  * two functions. As ComparatorDirectScoreTree creates pair of expression based on their score, we only need to do a
  * little modification in order to consider the Hole as a possible match, based on their type.
  * We choose then the function with the common tree having the higher score.
  *
  * We use this corpus function to fill the hole, and we replace the hole by the matching expression in the common tree.
  *
  * We return the holed function, the corpus function used to complete it, and the completed function (if there is some).
  *
  * IMPORTANT: at the moment the object if implemented to handle one and only one hole
  */
object Completor {

  case class Suggestion(expr: Option[Expr])


  def suggestCompletion(funDef: FunDef, corpus: ComparisonCorpus)(implicit context: LeonContext):
  (FunDef, Option[FunDef], Option[Expr]) = {
    val expr = funDef.body.get

    // for each function of corpus, search all roots of common tree that include the hole
    val funDefAndRoots = corpus.funDefs map (f => (f, possibleRootsWithHoles(f, expr)))

    // for each function of corpus, search all common tree respective to these roots
    // (filter only the ones containing the hole)
    val funDefAndTrees = funDefAndRoots map { p =>
      (p._1, p._2 flatMap possibleTrees filter hasHole)
    }

    // if no function match, return None
    if (funDefAndTrees.isEmpty)
      return (funDef, None, None)

    val suggestion = selectBestSuggestion(expr, funDefAndTrees)

    suggestion match {
      case None => (funDef, None, None)
      case Some(pair) => (funDef, Some(pair._1), Some(fillHole(expr, pair._2)))
    }
  }


  def possibleRootsWithHoles(funDefCorpus: FunDef, expr: Expr): List[Value] =
    possibleRoots(funDefCorpus.body.get, expr) filter (e => Utils.hasHole(e.b))

  def getBody(funDef: FunDef): Expr = funDef.body.get

  def hasHole(tree: FuncTree[Value]): Boolean = {
    tree.toList map (p => p.b) exists (e => e.isInstanceOf[Choose])
  }


  /**
    * select the best suggestion to fill the hole i.e. the common tree having the higher score between all the common
    * trees and all the function of corpus
    *
    * @param funDefAndTrees
    * @return
    */
  def selectBestSuggestion(expr: Expr, funDefAndTrees: List[(FunDef, List[FuncTree[Value]])]):
  Option[(FunDef, Expr)] = {
    val funDefAndBestTree = funDefAndTrees map { p =>
      (p._1, selectBestTreeOption(p._2, expr, getBody(p._1)))
    }

    selectBestFun(funDefAndBestTree) match {
      case None => None
      case Some(pair) => Some(pair._1, findPairOfTheHole(pair._2))
    }
  }

  def selectBestTreeOption(list: List[FuncTree[Value]], exprA: Expr, exprB: Expr): Option[(FuncTree[Value], Double)] = list match {
    case Nil => None
    case x :: xs => Some(selectBestTree(list, exprA, exprB))
  }

  def selectBestFun(list: List[(FunDef, Option[(FuncTree[Value], Double)])]): Option[(FunDef, FuncTree[Value])] = {
    val listWithScore = list filterNot (p => p._2.isEmpty)

    listWithScore match {
      case Nil => None
      case x :: xs => {
        val best = listWithScore.sortBy(p => -p._2.get._2).head
        Some(best._1, best._2.get._1)
      }
    }
  }

  def scoreOptionTree(tree: Option[FuncTree[Value]]): Double = tree match {
    case None => 0.0
    case Some(t) => geometricMean(t)
  }


  /**
    * Find in common tree the value that paired the hole and the expression from the corpus. The hole will be filled
    * with this hole
    *
    * @param tree
    * @return
    */
  def findPairOfTheHole(tree: FuncTree[Value]): Expr =
    (tree.toList filter (p => p.b.isInstanceOf[Choose])).head.a

  /**
    * Travers recursively the tree until finding the hole and replace it by
    * the wished expression.
    *
    * @param exprToFill
    * @param corpus
    * @return
    */
  def fillHole(exprToFill: Expr, corpus: Expr): Expr = {
    val filledTree = ExprOps.preMap {
      case Choose(expr) => Some(corpus)
      case _ => None
    }(exprToFill)

    filledTree
  }


}
