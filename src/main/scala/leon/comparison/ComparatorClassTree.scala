package leon.comparison

import leon.{GlobalOptions, LeonContext, utils}
import leon.comparison.Utils._
import leon.purescala.Expressions._


/**
  * Created by joachimmuth on 12.05.16.
  *
  * Go through both trees in parallel and compare each expression based on its class. Try to find the biggest
  * common tree.
  *
  * Procedure:
  * - Find all possible pair of roots. Then consider all children of both roots, and check which are
  * similar.
  * - Consider all possible combinations of children and repeat the same operation on them.
  * - Pick the biggest tree in the list of all possible similar tree
  * - Remove the tree overlapping the one chosen, and search if it exists an other common tree. Repeat.
  * - End with all common and exclusive common tree shared by trees A and B
  *
  * The MatchScore is calculated with the size of the common tree, compared with the sizes of trees A and B.
  */
object ComparatorClassTree extends Comparator {
  val name: String = "ClassTree"


  def compare(exprCorpus: Expr, expr: Expr)(implicit context: LeonContext) = {
    implicit val debugSection = utils.DebugSectionComparison
    val roots = possibleRoots(exprCorpus, expr)

    val trees = roots.flatMap(possibleTrees(_))
    val exclusives = exclusivesTrees(trees)
    val sum = exclusives.foldLeft(0)((acc, tree) => acc + tree.size)

    val listClassesA = collectClass(exprCorpus)
    val listClassesB = collectClass(expr)

    val score = matchScore(sum, listClassesA.size, listClassesB.size)

    if (context.findOption(GlobalOptions.optDebug).isDefined) {
      context.reporter.debug("---------------------")
      context.reporter.debug("COMPARATOR " + name)
      context.reporter.debug("Expressions: \n" + exprCorpus + expr)
      context.reporter.debug("Common Tree: \n" + exclusives)
      context.reporter.debug("---------------------")
    }

    (score, "")
  }

  /**
    * Extract all non-overlapping trees, in size order
    *
    * @param trees
    * @return
    */
  def exclusivesTrees(trees: List[myTree[(Expr, Expr)]]): List[myTree[(Expr, Expr)]] = trees match {
    case Nil => Nil
    case x :: xs =>
      val biggest = trees.sortBy(-_.size).head
      val rest = trees.filter(tree => flatList(tree).intersect(flatList(biggest)).isEmpty)
      List(biggest) ++ exclusivesTrees(rest)
  }

  def flatList(tree: myTree[(Expr, Expr)]): List[Expr] = tree.toList.flatMap(p => List(p._1, p._2))

  /**
    * list of all similar pair of expressions, based on classes.
    *
    * @param exprCorpus
    * @param expr
    * @return
    */
  def possibleRoots(exprCorpus: Expr, expr: Expr): List[(Expr, Expr)] = {
    val expressionsA = collectExpr(exprCorpus)
    val expressionsB = collectExpr(expr)

    val pairOfPossibleRoots = for {
      exprA <- expressionsA
      exprB <- expressionsB
      if areSimilar(exprA.getClass, exprB.getClass)
    } yield {
      (exprA, exprB)
    }

    pairOfPossibleRoots
  }


  /**
    * With a pair of roots, find all children and find all combination of matching children in order to create a list
    * of all possible matching tree. Then recursively call itself on each pair of children.
    *
    * @param pair of matching root
    * @return ether a Leaf or a List of all possible similar trees starting with this pair of roots
    */
  def possibleTrees(pair: (Expr, Expr)): List[myTree[(Expr, Expr)]] = {
    val exprA = pair._1
    val exprB = pair._2
    val childrenA = getChildren(exprA)
    val childrenB = getChildren(exprB)


    val pairOfMatchingChildren = findPairOfMatchingChildren(childrenA, childrenB)
    val combinationOfChildren = combineChildren(pairOfMatchingChildren)


    if (pairOfMatchingChildren.isEmpty) {
      List(myTree(pair, List()))
    } else {
      combinationOfChildren.foldLeft(List(): List[myTree[(Expr, Expr)]])(
        (listOfTree, children) => listOfTree ++ treesWithChildCombination(pair, children.map(p => possibleTrees(p)))
      )
    }
  }

  def findPairOfMatchingChildren(childrenA: List[Expr], childrenB: List[Expr]): List[(Expr, Expr)] = {
    for {
      childA <- childrenA
      childB <- childrenB
      if areSimilar(childA.getClass, childB.getClass)
    } yield {
      (childA, childB)
    }
  }

  /** All possible combination of pairs of children, given the condition that one child can only be used once.
    *
    * IMPROVEMENT: Here, it would be possible to already filter some cases.
    * When we do the combination, we try all cases, using one pair of matching, two, three, ... we could only keep the
    * ones using maximum of possible children, as we only want the biggest tree.
    *
    * @param pairs
    * @return
    */
  def combineChildren(pairs: List[(Expr, Expr)]): List[List[(Expr, Expr)]] = {
    combine(pairs).filterNot(p => isSameChildUsedTwice(p)).toList
  }

  def isSameChildUsedTwice(list: List[(Expr, Expr)]): Boolean = {
    list.map(_._1).distinct.size != list.size ||
      list.map(_._2).distinct.size != list.size
  }

  def combine(in: List[(Expr, Expr)]): Seq[List[(Expr, Expr)]] = {
    for {
      len <- 1 to in.length
      combinations <- in combinations len
    } yield combinations
  }

  /**
    * As we recursively call the method, children will create list of possibilities, as the root does. All this possible
    * combination need to be transformed into a list of complete tree.
    *
    * Technically, we have a combination of Children that return each a list of possible trees. So the upper-level tree
    * (whom root is named pair) can have all possible combination of theses lists as children.
    *
    * @param pair
    * @param listChildren
    * @return
    */
  def treesWithChildCombination(pair: (Expr, Expr), listChildren: List[List[myTree[(Expr, Expr)]]]): List[myTree[(Expr, Expr)]] = {
    def combine(list: List[List[myTree[(Expr, Expr)]]]): List[List[myTree[(Expr, Expr)]]] = list match {
      case Nil => List(Nil)
      case x :: xs =>
        for {
          j <- combine(xs)
          i <- x
        } yield i :: j
    }

    combine(listChildren).map(children => myTree(pair, children))
  }


  def areSimilar(getClass: Class[_ <: Expr], getClass1: Class[_ <: Expr]) = {
    getClass == getClass1
  }

}
