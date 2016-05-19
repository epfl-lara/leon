package leon.comparison

import leon.purescala.Expressions.{Expr, MatchExpr}
import leon.comparison.Utils._

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

    if (score > 0.0 && ComparisonPhase.debug){
      println("---------------------")
      println("COMPARATOR " + name)
      println("Expressions: ", expr_base, expr)
      println("---------------------")
    }

    score
  }


  def computeScore(tree: myTree[(Expr, Expr)]): Double = {
    // matching one of the elements is enough, because the tree comes from a ComparatorByClassTree
    val score = tree.value._1 match {
      case x: MatchExpr => 1.0
      case _ => 0.0

    }

    // if tree is a node, recursively travers children. If it is a leaf, just return the score
    tree.children.foldLeft(score)( (acc, child) => acc * computeScore(child))
  }
}
