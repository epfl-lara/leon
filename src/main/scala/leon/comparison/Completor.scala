package leon.comparison

import leon.purescala.Definitions.FunDef
import leon.purescala.Expressions._
import leon.comparison.Utils._
import leon.comparison.Scores._

/**
  * Created by joachimmuth on 08.06.16.
  *
  * Only accept ONE hole for the moment
  */
object Completor {
  case class Suggestion(expr: Option[Expr])
  case class Value(x: Expr, y: Expr, score: Double)


  def suggestCompletion(funDef: FunDef, corpus: ComparisonCorpus): (FunDef, Option[FunDef], Option[Expr]) = {
    val exprsCorpus = corpus.funDefs map(_.body.get)
    val expr = funDef.body.get

    // for each function of corpus, search all roots of common tree
    val funDefAndRoots = corpus.funDefs map(f => (f, possibleRoots(f, expr)))

    // for each function of corpus, search all common tree respective to these roots
    // (filter only the ones containing the hole)
    val funDefAndTrees = funDefAndRoots map {p =>
      (p._1, p._2 flatMap possibleTrees filter hasHole)
    }

    if (funDefAndTrees.isEmpty)
      return (funDef, None, None)

    val suggestion = chooseBestSuggestion(funDefAndTrees)

    suggestion match {
      case None => (funDef, None, None)
      case Some(pair) => (funDef, Some(pair._1), Some(pair._2))
    }
  }



  def possibleRoots(funDef: FunDef, expr: Expr): List[(Expr, Expr, Double)] =
    ComparatorDirectScoreTree.possibleRoots(funDef.body.get, expr) filter (e => Utils.hasHole(e._2))

  def getBody(funDef: FunDef): Expr = funDef.body.get

  def hasHole(tree: myTree[(Expr, Expr, Double)]): Boolean =
    tree.toList map(p => p._2) exists (e => e.isInstanceOf[Choose])



  def chooseBestSuggestion(funDefAndTrees: List[(FunDef, List[myTree[(Expr, Expr, Double)]])]):
  Option[(FunDef, Expr)] = {
    val funDefAndBestTree = funDefAndTrees map { p =>
      (p._1, selectBestTree(p._2))
    }

    selectBestFun(funDefAndBestTree) match {
      case None => None
      case Some(pair) => Some(pair._1, findPairOfTheHole(pair._2))
    }
  }

  def findPairOfTheHole(tree: myTree[(Expr, Expr, Double)]): Expr =
    (tree.toList filter (p => p._2.isInstanceOf[Choose])).head._1


  def selectBestTree(list: List[myTree[(Expr, Expr, Double)]]): Option[myTree[(Expr, Expr, Double)]] = list match{
    case Nil => None
    case x::xs => Some(list.sortBy(t => ComparatorDirectScoreTree.scoreTree(t)).head)
  }

  def selectBestFun(list: List[(FunDef, Option[myTree[(Expr, Expr, Double)]])]):
  Option[(FunDef, myTree[(Expr, Expr, Double)])] = {
    val (bestFun, bestTree) = ( list sortBy(p => -scoreOptionTree(p._2))  ).head

    bestTree match {
      case Some(tree) => Some(bestFun, tree)
      case None => None
    }
  }

  def scoreOptionTree(tree: Option[myTree[(Expr, Expr, Double)]]): Double = tree match {
    case None => 0.0
    case Some(t) => ComparatorDirectScoreTree.scoreTree(t)
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
      score = ComparatorDirectScoreTree.computeScore(exprA, exprB)
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
    val combinationOfChildren = combineChildren(pairOfMatchingChildren) // here we search for hole


    if(pairOfMatchingChildren.isEmpty) {
      List(myTree(value, List()))
    } else {
      combinationOfChildren.foldLeft(List(): List[myTree[(Expr, Expr, Double)]]) (
        (listOfTrees, children) => listOfTrees ++
          ComparatorDirectScoreTree.flatCombination(value, children.map(p => possibleTrees(p)))
      )
    }
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
    * @param exprB: comes form program argument! Can have a hole
    * @return
    */
  def computeScore(exprA: Expr, exprB: Expr): Double = (exprA, exprB) match {
    case (x, y: Choose) if x.getType == y.getType => 1.0
    case (x, y: Choose) => 0.0
    case (x: MatchExpr, y: MatchExpr) => scoreMatchExpr(x, y)
    case (x: CaseClass, y: CaseClass) => scoreCaseClass(x, y)
    case (x, y) if x.getClass == y.getClass =>
      1.0
    case _ => 0.0
  }










}
