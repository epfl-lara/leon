package leon.comparison

import leon.purescala.Expressions._
import leon.comparison.Utils._


/**
  * Created by joachimmuth on 12.05.16.
  *
  * Go through two tree in parallel and compare each expression based on its class. Try to find the biggest common tree.
  * Find all possible pair of roots. Then consider all children of both roots, and check which are
  * similar. Consider all possible combinations of children and repeate the same operation on them.
  *
  * We end up with a list of all possible similar tree and we pick the biggest one.
  *
  * The MatchScore is calculated with the size of the common tree, compared with the sizes of both trees.
  */
object ComparatorByClassTree extends Comparator{
  val name: String = "ClassTree"


  def compare(expr_base: Expr, expr: Expr): Double = {
    val pairOfRoots = possibleRoots(expr_base, expr)

    val allPossibleTrees = pairOfRoots.flatMap(possibleTrees(_))
    val exclusives = exclusivesTrees(allPossibleTrees)
    val sum = exclusives.foldLeft(0)( (acc, tree) => acc + tree.size)

    val listClassesB = collectClass(expr_base)
    val listClasses = collectClass(expr)

    val score = matchScore(sum, listClassesB.size, listClasses.size)

    if (score > 0.0 && ComparisonPhase.debug){
      println("---------------------")
      println("COMPARATOR " + name)
      println("Expressions: ", expr_base, expr)
      println("Common Tree: ", exclusives)
      println("---------------------")
    }

    score
  }

  /**
    * Extract all non-overlapping trees, in size order
    * @param trees
    * @return
    */
  def exclusivesTrees(trees: List[myTree[(Expr, Expr)]]): List[myTree[(Expr, Expr)]] = trees match {
    case Nil => Nil
    case x :: xs =>
      val biggest = trees.sortBy(-_.size).head
      val rest = trees.filter(tree => flatList(tree).intersect( flatList(biggest) ).isEmpty)
      List(biggest) ++ exclusivesTrees(rest)
  }

  def flatList(tree: myTree[(Expr, Expr)]): List[Expr] = tree.toList.flatMap(p => List(p._1, p._2))

  /**
    * list of all similar pair of expressions, based on classes.
    *
    * @param expr_base
    * @param expr
    * @return
    */
  def possibleRoots(expr_base: Expr, expr: Expr): List[(Expr, Expr)] = {
    val expressionsBase = collectExpr(expr_base)
    val expressions = collectExpr(expr)

    val pairOfPossibleRoots = for {
      expBase <- expressionsBase
      exp <- expressions
      if areSimilar(expBase.getClass, exp.getClass)
    } yield {
      (expBase, exp)
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
