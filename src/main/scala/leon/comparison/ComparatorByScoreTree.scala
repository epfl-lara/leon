package leon.comparison

import leon.purescala.Expressions._
import leon.comparison.Utils._
import leon.purescala.Common.Tree

/**
  * Created by joachimmuth on 19.05.16.
  *
  * Will be my best comparator
  * Travers again a Common Tree created by "ClassTree" comparator and give it a score, after finer analysis
  */
object ComparatorByScoreTree extends Comparator {
  override val name: String = "ScoreTree"



  def compare(expr_base: Expr, expr: Expr): Double = {
    val pairOfRoots = ComparatorByClassTree.possibleRoots(expr_base, expr)

    val allPossibleTrees = pairOfRoots.flatMap(ComparatorByClassTree.possibleTrees(_))
    val biggest = allPossibleTrees.sortBy(-_.size).head

    val score:Double = computeScore(biggest)
    val normalizedScore = normalize(score, biggest.size)

    if (score > 0.0 && ComparisonPhase.debug){
      println("---------------------")
      println("COMPARATOR " + name)
      println("Expressions: ", expr_base, expr)
      println("---------------------")
    }

    normalizedScore
  }

  /**
    * Geometric mean of obtained score, to balance the difference between small and big tree.
    *
    * @param score
    * @param n: size of tree
    * @return
    */
  def normalize(score: Double, n: Int) = Math.pow(score, 1 / n.toDouble)


  /**
    * Give a score to each pair of expression. In combination with "normalize" function, do a Geometric Mean on this
    * score. They all have the same weight.
    *
    * @param tree
    * @return
    */
  def computeScore(tree: myTree[(Expr, Expr)]): Double = {
    // matching one of the elements is enough, because the tree comes from a ComparatorByClassTree
    val score = tree.value match {
      case (x: MatchExpr, y: MatchExpr) => scoreMatchExpr(x, y)
      case _ => 1.0

    }

    // if tree is a node, recursively travers children. If it is a leaf, just return the score
    tree.children.foldLeft(score)( (acc, child) => acc * computeScore(child))
  }

  // TODO
  def scoreMatchExpr(x: MatchExpr, y: MatchExpr): Double = {
    /**
      * compare only the MatchCases conditions, not the returned value, which are compared through main compareExp
      * function
      *
      * @return
      */
    def scoreMatchCase(casesB: Seq[MatchCase], cases: Seq[MatchCase]): Double = {
      val mapCasesB = toMap(casesB)
      val mapCases = toMap(cases)
      compareMap(mapCasesB, mapCases)
    }

    /**
      * Compare the map containing the MatchCases
      * NOW: just check how many similar key they have
      * NEXT: do a mean between the pattern AND the result and iterate on the result expression
      *
      * @param mapCasesB
      * @param mapCases
      * @return
      */
    def compareMap(mapCasesB: Map[Tree, Expr], mapCases: Map[Tree, Expr]): Double = {
      val all = mapCasesB.keys.size + mapCases.keys.size.toDouble
      val diff = ((mapCasesB.keySet -- mapCases.keySet) ++ (mapCases.keySet -- mapCasesB.keySet)).size.toDouble
      (all - diff) / all
    }

    def toMap(cases: Seq[MatchCase]) = {
      cases.map(a => a.pattern match {
        case InstanceOfPattern(_, ct) => ct -> a.rhs
        case CaseClassPattern(_, ct, _) => ct -> a.rhs
        case _ => a.pattern -> a.rhs
      }).toMap
    }

    1.0
  }


}
