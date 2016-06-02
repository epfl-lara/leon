package leon.comparison
import leon.purescala.Expressions.{CaseClassPattern, _}
import leon.comparison.Utils._
import leon.purescala.Common.Tree
import leon.purescala.Definitions.{CaseClassDef, ClassDef}
import leon.purescala.Types.{ClassType, TypeTree}
import leon.comparison.Scores._

/**
  * Created by joachimmuth on 02.06.16.
  *
  * Travers in parallel two trees. Instead of comparing Class like in ClassTree, we directly compute a score of the pair
  * like in ScoreTree. This allow the most flexible comparison.
  *
  * Additionally, we will handle holes like "???" of "choose", and try to assign them an expression of the other tree.
  *
  * For practical reasons, we suppose that "base" trees (i.e. tree extracted from examples collection, always first in
  * function arguments) have no holes. Indeed, these trees are suppose to come from a valid collection with which the
  * user compare its "draft" tree.
  */
object ComparatorByScoreTreeWithHoles extends Comparator{
  override val name: String = "ScoreTreeWtHoles"

  override def compare(expr_base: Expr, expr: Expr): Double = {
    val roots = possibleRoots(expr_base, expr)

    0.0
  }

  /**
    * All possible root for our common tree, and the score of the pair
    * @param expr_base
    * @param expr
    * @return
    */
  def possibleRoots(expr_base: Expr, expr: Expr): List[(Expr, Expr, Double)] = {
    val expressionsBase = collectExpr(expr_base)
    val expressions = collectExpr(expr)

    val pairOfPossibleRoots = for {
      expBase <- expressionsBase
      exp <- expressions
      if computeScore(expBase, exp) > 0.0
    } yield {
      (expBase, exp, computeScore(expBase, exp))
    }

    pairOfPossibleRoots
  }

  def computeScore(exprA: Expr, exprB: Expr): Double = (exprA, exprB) match {
    case (x: MatchExpr, y: MatchExpr) => scoreMatchExpr(x, y)
    case (x: CaseClass, y: CaseClass) => scoreCaseClass(x, y)
    case (x, y) if x.getClass == y.getClass =>
      1.0
    case _ => 0.0
  }



  def computeScore(tree: myTree[(Expr, Expr)]): Double = {
    // we treat each type differently with its proper scorer, stores in object Scores
    val score = tree.value match {
      case (x: MatchExpr, y: MatchExpr) => scoreMatchExpr(x, y)
      case (x: CaseClass, y: CaseClass) => scoreCaseClass(x, y)
      case _ => 1.0

    }

    // if tree is a node, recursively travers children. If it is a leaf, just return the score
    // we process a geometrical mean
    tree.children.foldLeft(score)( (acc, child) => acc * computeScore(child))
  }


  /**
    * With a pair of roots, find all children and find all combination of matching children in order to create a list
    * of all possible matching tree. Then recursively call itself on each pair of children.
    *
    * @param pair of matching root
    * @return ether a Leaf or a List of all possible similar trees starting with this pair of roots
    */
  def possibleTrees(pair: (Expr, Expr)): List[myTree[(Expr, Expr)]] = {
    val exprBase = pair._1
    val expr = pair._2
    val childrenBase = getChildren(exprBase)
    val children = getChildren(expr)


    val pairOfMatchingChildren = findPairOfMatchingChildren(childrenBase, children)
    val combinationOfChildren = combineChildren(pairOfMatchingChildren)


    if(pairOfMatchingChildren.isEmpty) {
      List(myTree(pair, List()))
    } else {
      combinationOfChildren.foldLeft(List(): List[myTree[(Expr, Expr)]])(
        (listOfTree, children) => listOfTree ++ treesWithChildCombination(pair, children.map(p => possibleTrees(p)))
      )
    }
  }



  def findPairOfMatchingChildren(childrenBase: List[Expr], children: List[Expr]): List[(Expr, Expr)] = {
    for{
      childBase <- childrenBase
      child <- children
      if areSimilar(childBase.getClass, child.getClass)
    } yield {
      (childBase, child)
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
