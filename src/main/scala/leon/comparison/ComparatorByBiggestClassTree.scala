package leon.comparison

import leon.purescala.Expressions._
import leon.comparison.Utils._

/**
  * Created by joachimmuth on 05.05.16.
  *
  * In contrary of the comparator by List of Expressions, in which each Expr contains its whole tree of children,
  * when we compare type of Expressions between them, we loose the information about children.
  *
  * This is a variation of ComparatorByListType where we check what is the longest sequence of same type.
  *
  */
object ComparatorByBiggestClassTree extends Comparator {
  val name: String = "BiggestClassTree"

  def compare(expr_base: Expr, expr: Expr) = {
    val sizeBiggestTree: Int = biggestSimilarClassTree(expr_base, expr)

    val listClassesB = collectClass(expr_base)
    val listClasses = collectClass(expr)

    (matchScore(sizeBiggestTree, listClassesB.size, listClasses.size), "")
  }


  def biggestSimilarClassTree(exprB: Expr, expr: Expr): Int = {
    val listSimilarTree = similarClassTree(exprB, expr)
    0
  }



  def similarClassTree(exprB: Expr, expr: Expr) = {
    val pathes = similarPathesInClassTree(exprB, expr)

    println("expressions")
    println(exprB)
    println(expr)
    println("lists")
    pathes map (println(_))

    val trees = possibleTrees(pathes)

    //val cleanPathes = removeDuplicates(pathes)
    0
  }


  def possibleTrees(pathes: List[List[(Expr, Expr)]]) = {
    println("possibleTrees")
    /**
      *
      * @param pathes
      * @param acc is List(listOfParents, listOfChidren)
      */
    def helper(pathes: List[List[(Expr, Expr)]]) ={
      val grouped = pathes.groupBy(p => p.head)
      val groupedChildren = grouped.mapValues(p => p.map(_.tail))
      println("grouped")
      println(grouped)
      println("groupedChildren")
      println(groupedChildren)
      val nCombination =
      groupedChildren.mapValues(p => Math.min(p.map(_.head._1).distinct.size, p.map(_.head._2).distinct.size))
      println(nCombination)
      val combinations = groupedChildren.mapValues(p => p.toSet.subsets(nCombinations(p)).map(_.toList).toList)
      println("combinations")
      println(combinations)

      val filtered = combinations.mapValues(p => p.filter(q => isDistinct(q.map(l => l.head._1))))
      println("filtered")
      println(filtered)
      val filtered2 = filtered.mapValues(p => p.filter(q => isDistinct(q.map(l => l.head._2))))
      println("filtered2")
      println(filtered2)

      println(" group ??")
      println(filtered2(pathes.head.head).head)
      println(filtered2(pathes.head.head).head.groupBy(_.head))
      println(filtered2(pathes.head.head).head.groupBy(_.head).mapValues(p => p.map(_.tail)))
      println(filtered2(pathes.head.head).head.groupBy(_.head).mapValues(p => p.map(_.tail).isEmpty))
    }
    helper(pathes)
    0
  }

  def isDistinct(exprs: List[Expr]): Boolean = exprs.size == exprs.distinct.size

  def nCombinations(p: List[List[(Expr, Expr)]]): Int ={
    println(Math.min(p.map(_.head._1).distinct.size, p.map(_.head._2).distinct.size))
    Math.min(p.map(_.head._1).distinct.size, p.map(_.head._2).distinct.size)
  }





  /**
    * We define a "duplicate" as two path wo take the same way, but in one moment an Expression match two. In this case
    * we must chose the one we want to match with, and delete the other(s).
    *
    * @param pathes
    * @return
    */
  def removeDuplicates(pathes: List[List[(Expr, Expr)]]) = {
    def helper(pathes: List[List[(Expr, Expr)]]) = {
      val grouped = pathes.groupBy(p => (p.dropRight(1), p.last._1))

      val (duplicates, nonduplicate) = grouped.partition(p => p._2.size > 1)

      println("remove duplicate")
      grouped.map(println(_))
      println("duplcates")
      duplicates.map(println(_))
      println("nonduplicates")
      nonduplicate.map(println(_))

      val fixedDuplicates = removeOneByOne(duplicates.toList, Nil)

      println("fixed")
      fixedDuplicates.map(println(_))
    }

    helper(pathes)
  }

  /**
    * Take the first duplicate problem, choose the "best option" (largest path)
    *
    * @param list
    * @param acc
    * @return
    */
  def removeOneByOne(list: List[((List[(Expr, Expr)], Expr), List[List[(Expr, Expr)]])],
                     acc: List[List[(Expr, Expr)]]): List[List[(Expr, Expr)]] = list match {
    case Nil => acc
    case x :: xs if x._2.isEmpty =>
      removeOneByOne(xs, acc)
    case x :: xs =>
      val temp = biggestList(x._2)
      val usedValue = temp.head.last._2
      val restOption = xs.map(p => (p._1, p._2 filter(q => (p._1._1 != x._1._1 || q.last._2 != usedValue))))
      removeOneByOne(restOption, acc ++ temp)
  }

  def biggestList(list : List[List[(Expr, Expr)]]): List[List[(Expr, Expr)]] = list match {
    case Nil => Nil
    case x :: y :: xs => biggestList( (if (x.size > y.size) x else y) :: xs )
    case x :: xs => List(x)
  }

  /**
    * This function traverse in parallel two tree, in order to find similarities between their structure. It only
    * consider the CaseClass of each Expr and the hierarchy.
    *
    * Each pair of Expr, whose classes match together, are stored in the ancestors
    * Ancestors represent a list that record all matching parent of the current Expr. It represent a "path" from the
    *   current Expr to the farthest similar ancestor.
    * Finally, the function returns a list of all possible similar tree.
    *
    * E.g: tree1 = {a , {{b, Nil}, {c, Nil}}}    tree2 = {x , {{y, Nil}, {z, Nil}}}
    * will return two lists: List((a, x), (b, y))  and  List((a, x), (c, z))
    *
    * E.g: tree1 = {a, {b, {c, Nil}}}       tree2 = {x, {y, {z, Nil}}}
    * will return one list: List((a, x), (b, y), (c, z))
    *
    * Then, it is up to us to deal with these lists to recover the biggest possible similar tree.
    *
    * BEWARE: as we try all possible combinations, some Expr may match multiple time. In the first example, if b, c,
    * y and z are all of the same Class, the resulting lists will be
    * List((a, x), (b, y))   List((a, x), (b, z))   List((a, x), (c, y))   List((a, x), (c, z))
    * Which doesn't mean that
    * Pay attention to deal with it
    *
    * @param exprB
    * @param expr
    * @return
    */
  def similarPathesInClassTree(exprB: Expr, expr: Expr): List[List[(Expr, Expr)]] = {
    def helper(exprB: Expr, expr: Expr, ancestors: List[(Expr, Expr)]): List[List[(Expr, Expr)]] = {
      val childrenBase = getChildren(exprB)
      val children = getChildren(expr)

      (childrenBase, children) match {

        // both trees reach leaves
        case (Nil, Nil) if exprB.getClass == expr.getClass =>
          List(ancestors :+ (exprB, expr))
        case (Nil, Nil) =>
          List(ancestors)

        // one of the tree reaches leaf
        case (Nil, _) if exprB.getClass == expr.getClass =>
          ancestors +: (for(child <- children) yield helper(exprB, child, Nil)).flatten
        case (_, Nil) if exprB.getClass == expr.getClass =>
          ancestors +: (for(childB <- childrenBase) yield helper(childB, expr, Nil)).flatten

        // both trees are in nodes
        case (_, _) if exprB.getClass == expr.getClass =>
          for{
            childBase <- childrenBase
            child <- children
          } yield {
            helper(childBase, child, ancestors :+ (exprB, expr))
          }.flatten
        case (_,_) =>
          val descendants = for {
            childBase <- exprB +: childrenBase
            child <- expr +: children
            if !(childBase == exprB && child == expr) //avoid re-comparison of the two parent
          } yield {
            helper(childBase, child, Nil)
          }.flatten

          ancestors +: descendants
      }
    }

    helper(exprB, expr, Nil)
  }






}
