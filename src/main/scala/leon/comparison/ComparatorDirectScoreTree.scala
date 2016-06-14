package leon.comparison
import leon.{GlobalOptions, LeonContext}
import leon.comparison.Scores._
import leon.comparison.Utils._
import leon.purescala.Expressions._

/**
  * Created by joachimmuth on 02.06.16.
  *
  * Travers in parallel two trees. Instead of comparing Class like in ClassTree, we directly compute a score of the pair
  * like in ScoreTree. This allow the most flexible comparison.
  *
  */
object ComparatorDirectScoreTree extends Comparator {
  override val name: String = "DirectScoreTree"


  override def compare(exprCorpus: Expr, expr: Expr)(implicit context: LeonContext): (Double, String) = {
    val roots = possibleRoots(exprCorpus, expr)
    val trees = roots.flatMap(possibleTrees(_))
    if (trees.isEmpty) return (0.0, "")

    val (bestTree, score) = selectBestTree(trees, exprCorpus, expr)

    if (context.findOption(GlobalOptions.optDebug).isDefined){
      println("---------------------")
      println("COMPARATOR " + name)
      println("Expressions: ", exprCorpus, expr)
      println("Common Tree: ", bestTree)
      println("---------------------")
    }

    (score, " (" + bestTree.size + ")")
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
  def pairAndScoreExpr(exprsA: List[Expr], exprsB: List[Expr]): List[Value] = {
    val pairOfExprs = for {
        exprA <- exprsA
        exprB <- exprsB
        score = computeScore(exprA, exprB)
      if score > 0.0
    } yield {
      Value(exprA, exprB, score)
    }

    pairOfExprs
  }

  def possibleRoots(exprA: Expr, exprB: Expr): List[Value] = {
    val exprsA = collectExpr(exprA)
    val exprsB = collectExpr(exprB)

    pairAndScoreExpr(exprsA, exprsB)
  }

  def matchChildren(childrenA: List[Expr], childrenB: List[Expr]): List[Value] =
    pairAndScoreExpr(childrenA, childrenB)



  /**
    * With a pair of roots, find all children and find all combination of matching children in order to create a list
    * of all possible matching tree. Then recursively call itself on each pair of children.
    *
    * @param value of root
    * @return ether a Leaf or a List of all possible similar trees starting with this pair of roots
    */
  def possibleTrees(value: Value): List[myTree[Value]] = {
    val exprA = value.a
    val exprB = value.b
    val childrenA = getChildren(exprA)
    val childrenB = getChildren(exprB)


    val pairOfMatchingChildren = matchChildren(childrenA, childrenB)
    val combinationOfChildren = combineChildren(pairOfMatchingChildren)


    if(pairOfMatchingChildren.isEmpty) {
      List(myTree(value, List()))
    } else {
      combinationOfChildren.foldLeft(List(): List[myTree[Value]])(
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
    case (x, y: Choose) => 0.1
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
  def combineChildren(pairs: List[Value]): List[List[Value]] = {
    combine(pairs).filterNot(p => isSameChildUsedTwice(p)).toList
  }

  def isSameChildUsedTwice(list: List[Value]): Boolean = {
    list.map(_.a).distinct.size != list.size ||
      list.map(_.b).distinct.size != list.size
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
    * Normalize a score of the tree
    *
    * Must pay attention to the fact that small trees will always be chosen. To balance that: consider the size of the
    * tree and the size of the compared expression to create a "weight".
    *
    * @param tree
    * @return
    */

  def normalizedScoreTree(tree: myTree[Value], exprA: Expr, exprB: Expr): Double = {
    val scoreTree = geometricMean(tree)
    val sizeA = collectExpr(exprA).size.toDouble
    val sizeB = collectExpr(exprB).size.toDouble
    val weight = (1 / Math.max(sizeA, sizeB)) * tree.size.toDouble

    scoreTree * weight
  }

  def geometricMean(tree: myTree[Value]): Double =
    Math.pow(tree.toList.foldLeft(1.0)((acc, tree) => acc * tree.score), 1/ tree.size.toDouble)

  def selectBestTree(trees: List[myTree[Value]], exprCorpus: Expr, expr: Expr) = {
    val biggest = trees.sortBy(t => -normalizedScoreTree(t, exprCorpus, expr)).head
    val score = normalizedScoreTree(biggest, exprCorpus, expr)
    (biggest, score)
  }


}
