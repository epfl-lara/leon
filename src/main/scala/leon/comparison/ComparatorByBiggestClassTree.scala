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
object ComparatorByBiggestClassTree {
  val name: String = "BiggestClassTree"

  def compare(expr_base: Expr, expr: Expr): Double = {
    val sizeBiggestTree: Int = biggestSimilarClassTree(expr_base, expr)

    val listClassesB = collectClass(expr_base)
    val listClasses = collectClass(expr)

    percentBetweenTwo(sizeBiggestTree, listClassesB.size, listClasses.size)
  }


  def biggestSimilarClassTree(exprB: Expr, expr: Expr): Int = {
    val listSimilarTree = similarClassTree(exprB, expr)
    0
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
  def similarClassTree(exprB: Expr, expr: Expr): List[List[(Expr, Expr)]] = {
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
