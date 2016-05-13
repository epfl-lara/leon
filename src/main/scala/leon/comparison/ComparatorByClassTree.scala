package leon.comparison

import leon.purescala.Expressions._
import leon.comparison.Utils._


/**
  * Created by joachimmuth on 12.05.16.
  *
  * New attempt to find similar tree shared by two Expressions-Tree.
  * Again, (as in ComparatorByBiggestClassTree) we compare the classes of the expression.
  * But this time, instead of searching similar paths, and then trying to recompose a tree, we search all possible
  * roots, and then, from each root, we search all similar tree possibles.
  */
object ComparatorByClassTree extends Comparator{
  val name: String = "ClassTree"

  def compare(expr_base: Expr, expr: Expr): Double = {
    val pairOfRoots = possibleRoots(expr_base, expr)

    val allPossibleTrees = pairOfRoots.flatMap(possibleTrees(_))
    val biggestTree = allPossibleTrees.sortBy(- _.size).head

    println(biggestTree)

    val listClassesB = collectClass(expr_base)
    val listClasses = collectClass(expr)

    percentBetweenTwo(biggestTree.size, listClassesB.size, listClasses.size)
  }



  def toTreeList(pair: (Expr, Expr), listChildren: List[List[Tree[(Expr, Expr)]]]): List[Tree[(Expr, Expr)]] = {
    def combine(list: List[List[Tree[(Expr, Expr)]]]): List[List[Tree[(Expr, Expr)]]] = list match {
      case Nil => List(Nil)
      case x :: xs =>
        for {
          j <- combine(xs)
          i <- x
        } yield i :: j
    }

    combine(listChildren).map(children => Tree(pair, children))
  }


  def possibleTrees(pair: (Expr, Expr)): List[Tree[(Expr, Expr)]] = {
    val exprBase = pair._1
    val expr = pair._2
    val childrenBase = getChildren(exprBase)
    val children = getChildren(expr)


    val pairOfMatchingChildren = pairOfChildren(childrenBase, children)
    val combinationOfChildren = combineChildren(pairOfMatchingChildren)


    if(pairOfMatchingChildren.isEmpty) {
      List(Tree(pair, List()))
    } else {
      combinationOfChildren.foldLeft(List(): List[Tree[(Expr, Expr)]])(
        (listOfTree, children) => listOfTree ++ toTreeList(pair, children.map(p => possibleTrees(p)))
      )
    }
  }


  def pairOfChildren(childrenBase: List[Expr], children: List[Expr]): List[(Expr, Expr)] = {
    for{
      childBase <- childrenBase
      child <- children
      if areSimilar(childBase.getClass, child.getClass)
    } yield {
      (childBase, child)
    }
  }

  /**
    * Here, it would be possible to already filter some cases.
    * When we do the combination, we try all cases, using one pair of matching, two, three, ... we could only keep the
    * ones using maximum of possible children, as we only want the biggest tree.
    * I don't do that for the moment, because maybe i'll search in smaller tree too later.
    * @param pairOfMatchingChildren
    * @return
    */
  def combineChildren(pairOfMatchingChildren: List[(Expr, Expr)]): List[List[(Expr, Expr)]] = {
    combine(pairOfMatchingChildren).filterNot(p => isSameChildUsedTwice(p)).toList
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
    * list of all similar pair of expressions, based on classes. Third element is "similarity" double, will be used
    * later
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

  def areSimilar(getClass: Class[_ <: Expr], getClass1: Class[_ <: Expr]) = {
    getClass == getClass1
  }

}
