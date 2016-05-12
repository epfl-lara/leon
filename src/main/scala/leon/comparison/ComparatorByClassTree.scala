package leon.comparison

import leon.purescala.Expressions._
import leon.comparison.Utils._

import scala.collection.GenTraversableOnce

/**
  * Created by joachimmuth on 12.05.16.
  *
  * New attempt to find similar tree shared by two Expressions-Tree.
  * Again, (as in ComparatorByBiggestClassTree) we compare the classes of the expression.
  * But this time, instead of searching similar paths, and then trying to recompose a tree, we search all possible
  * roots, and then, from each root, we search all similar tree possibles.
  */
object ComparatorByClassTree {
  val name: String = "BiggestClassTree"

  def compare(expr_base: Expr, expr: Expr): Double = {
    val pairOfRoots = possibleRoots(expr_base, expr)

    val sizeBiggestTree: Int = 0

    val listClassesB = collectClass(expr_base)
    val listClasses = collectClass(expr)

    percentBetweenTwo(sizeBiggestTree, listClassesB.size, listClasses.size)
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

  def combineChildren(pairOfMatchingChildren: List[(Expr, Expr)]): List[List[(Expr, Expr)]] = {
    combine(pairOfMatchingChildren).filterNot(p => isSameChildUsedTwice(p)).toList
  }


  def possibleTrees(pair: (Expr, Expr)): List[Tree[(Expr, Expr)]] = {
    val exprBase = pair._1
    val expr = pair._2
    val childrenBase = getChildren(exprBase)
    val children = getChildren(expr)

    val pairOfMatchingChildren = pairOfChildren(childrenBase, children)
    val combinationOfChildren = combineChildren(pairOfMatchingChildren)

    if(pairOfMatchingChildren.isEmpty)
      return List(Tree(pair, List()))


    combinationOfChildren.foldLeft(List(): List[Tree[(Expr, Expr)]])(
      (listOfTree, children) => listOfTree ++ BadTree(pair, children.map(p => possibleTrees(p))).toTreeList
    )
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
