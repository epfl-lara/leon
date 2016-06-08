package leon.comparison
import leon.comparison.Scores._
import leon.comparison.Utils._
import leon.purescala.Expressions._

/**
  * Created by joachimmuth on 02.06.16.
  *
  * Travers in parallel two trees. Instead of comparing Class like in ClassTree, we directly compute a score of the pair
  * like in ScoreTree. This allow the most flexible comparison.
  *
  * Additionally, we will handle holes like "???" or "choose", and try to assign them an expression of the other tree.
  *
  * For practical reasons, we suppose that corpus trees (i.e. tree extracted from examples collection) have no holes.
  * Indeed, these trees are suppose to come from a valid collection with which the user compare its "draft" tree.
  */
object ComparatorDirectScoreTree extends Comparator{
  override val name: String = "DirectScoreTree"

  case class Value(pair: (Expr, Expr), position: (Int, Int), score: Double)

  override def compare(expr_corpus: Expr, expr: Expr): (Double, String) = {
    val roots = possibleRoots(expr_corpus, expr)
    val trees = roots.flatMap(possibleTrees(_))
    if (trees.isEmpty) return (0.0, "")

    //val exclusive = exclusiveTrees(trees)
    //val scores = trees.map(t => (t, scoreTree(t))).sortBy(-_._2)
    val biggest = trees.sortBy(-_.size).head
    val score = scoreTree(biggest)

    (score, " (" + biggest.size + ")")
  }


  /**
    * Define whether a pair of expressions worth be combined (i.e its score is above 0.0%)
    * This is kind of a local optimization, instead of creating all possibles trees (what would be enormous).
    * The threshold can be modified.
    *
    * @param exprsA
    * @param exprsB
    * @return
    */
  def pairAndScoreExpr(exprsA: List[Expr], exprsB: List[Expr]): List[(Expr, Expr, Double)] = {
    val pairOfExprs = for {
        exprA <- exprsA
        exprB <- exprsB
        score = computeScore(exprA, exprB)
      if score > 0.0
    } yield {
      (exprA, exprB, score)
    }

    pairOfExprs
  }

  def possibleRoots(exprA: Expr, exprB: Expr): List[(Expr, Expr, Double)] = {
    val exprsA = collectExpr(exprA)
    val exprsB = collectExpr(exprB)

    pairAndScoreExpr(exprsA, exprsB)
  }

  def matchChildren(childrenA: List[Expr], childrenB: List[Expr]): List[(Expr, Expr, Double)] =
    pairAndScoreExpr(childrenA, childrenB)



  /**
    * With a pair of roots, find all children and find all combination of matching children in order to create a list
    * of all possible matching tree. Then recursively call itself on each pair of children.
    *
    * @param value of root
    * @return ether a Leaf or a List of all possible similar trees starting with this pair of roots
    */
  def possibleTrees(value: (Expr, Expr, Double)): List[myTree[(Expr, Expr, Double)]] = {
    val exprA = value._1
    val exprB = value._2
    val childrenA = getChildren(exprA)
    val childrenB = getChildren(exprB)


    val pairOfMatchingChildren = matchChildren(childrenA, childrenB)
    val combinationOfChildren = combineChildren(pairOfMatchingChildren)


    if(pairOfMatchingChildren.isEmpty) {
      List(myTree(value, List()))
    } else {
      combinationOfChildren.foldLeft(List(): List[myTree[(Expr, Expr, Double)]])(
      (listOfTrees, children) => listOfTrees ++ flatCombination(value, children.map(p => possibleTrees(p)))
      )
    }
  }



  /**
    * Distributes score computation according to expressions
    *
    * Allow some flexibilities, we can even compare two different expressions and give it a non-zero score.
    * We can also go though some expression to compare deeper proprieties, like:
    *   - order in if-else statement (TO DO)
    *   - exclusiveness of MatchCases in a case-match statement (TO DO)
    *   - value of the expression
    *   - ...
    *
    * @param exprA
    * @param exprB
    * @return
    */
  def computeScore(exprA: Expr, exprB: Expr): Double = (exprA, exprB) match {
    case (x: MatchExpr, y: MatchExpr) => scoreMatchExpr(x, y)
    case (x: CaseClass, y: CaseClass) => scoreCaseClass(x, y)
    case (x, y) if x.getClass == y.getClass =>
      1.0
    case _ => 0.0
  }




  /** All possible combination of pairs of children, given the condition that one child can only be used once.
    *
    * @param pairs
    * @return
    */
  def combineChildren(pairs: List[(Expr, Expr, Double)]): List[List[(Expr, Expr, Double)]] = {
    combine(pairs).filterNot(p => isSameChildUsedTwice(p)).toList
  }

  def isSameChildUsedTwice(list: List[(Expr, Expr, Double)]): Boolean = {
    list.map(_._1).distinct.size != list.size ||
      list.map(_._2).distinct.size != list.size
  }

  def combine[T](in: List[T]): Seq[List[T]] = {
    for {
      len <- 1 to in.length
      combinations <- in combinations len
    } yield combinations
  }



  /**
    * Intuition: As we recursively call the method, children will create list of possibilities, as the root does.
    * All this possible combination need to be transformed into a list of complete tree.
    *
    * Technical: we have a combination of Children that return each a list of possible trees. So the upper-level tree
    * (whom root is named pair) can have all possible combination of theses lists as children.
    *
    * @param value of root, in our case type is : (Expr, Expr, Double) i.e.
    * @param listChildren
    * @return
    */
  def flatCombination[T](value: T, listChildren: List[List[myTree[T]]]): List[myTree[T]] = {
    def combine(list: List[List[myTree[T]]]): List[List[myTree[T]]] = list match {
      case Nil => List(Nil)
      case x :: xs =>
        for {
          j <- combine(xs)
          i <- x
        } yield i :: j
    }

    combine(listChildren).map(children => myTree(value, children))
  }

  /**
    * Extract all non-overlapping trees, in size order
    *
    * @param trees
    * @return
    */
  def exclusiveTrees(trees: List[myTree[(Expr, Expr, Double)]]): List[myTree[(Expr, Expr, Double)]] = trees match {
    case Nil => Nil
    case x :: xs =>
      val biggest = trees.sortBy(-_.size).head
      val rest = trees.filter(tree => flatList(tree).intersect( flatList(biggest) ).isEmpty)
      List(biggest) ++ exclusiveTrees(rest)
  }

  def flatList(tree: myTree[(Expr, Expr, Double)]): List[Expr] = tree.toList.flatMap(p => List(p._1, p._2))

  /**
    * Geometric mean of all pair scores
    * "Normalization" in order not to overvalue small trees
 *
    * @param tree
    * @return
    */
  def scoreTree(tree: myTree[(Expr, Expr, Double)]): Double =
    Math.pow(tree.toList.foldLeft(1.0)((acc, tree) => acc * tree._3), 1/(tree.size.toDouble))


}
