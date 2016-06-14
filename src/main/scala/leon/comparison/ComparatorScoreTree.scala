package leon.comparison

import leon.{GlobalOptions, LeonContext, utils}
import leon.comparison.Utils._
import leon.purescala.Common.Tree
import leon.purescala.Definitions.{CaseClassDef, ClassDef}
import leon.purescala.Expressions._
import leon.purescala.Types.{ClassType, TypeTree}

/**
  * Created by joachimmuth on 19.05.16.
  *
  * This give a score to the biggest common tree found by ClassTree.
  * A common tree is composed by pair of expression (A, B) which have the same type, but are maybe not perfectly
  * equivalent.
  *
  * ScoreTree take each pair and compute a score for it, then make a geometrical mean over all these scores.
  * (The mean "balances" the fact that a big tree will always have a poorer score than a little)
  *
  * IMPORTANT: ScoreTree scores an already chosen common Tree, coming from ComparatorClassTree. A frequent 100% score
  * doesn't mean that FunDef match at 100%, but that the elements of this common Tree match at 100%
  *
  */
object ComparatorScoreTree extends Comparator {
  override val name: String = "ScoreTree"

  def compare(exprCorpus: Expr, expr: Expr)(implicit context: LeonContext): (Double, String) = {
    implicit val debugSection = utils.DebugSectionComparison
    val pairOfRoots = ComparatorClassTree.possibleRoots(exprCorpus, expr)
    val allPossibleTrees = pairOfRoots flatMap ComparatorClassTree.possibleTrees
    if (allPossibleTrees == Nil) return (0.0, "")

    val biggest = allPossibleTrees.sortBy(-_.size).head
    val score: Double = computeScore(biggest)
    val normalizedScore = normalize(score, biggest.size)

    if (context.findOption(GlobalOptions.optDebug).isDefined) {
      context.reporter.debug("---------------------")
      context.reporter.debug("COMPARATOR " + name)
      context.reporter.debug("Expressions: \n" + exprCorpus + "\n" + expr)
      context.reporter.debug("Biggest: \n" + biggest)
      context.reporter.debug("Score: \n" + score)
      context.reporter.debug("---------------------")
    }

    (normalizedScore, "")
  }

  /**
    * Geometric mean of obtained score, to balance the difference between small and big tree.
    *
    * @param score
    * @param n : size of tree
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
    // we treat each type differently with its proper scorer
    val score = tree.value match {
      case (x: MatchExpr, y: MatchExpr) => scoreMatchExpr(x, y)
      case (x: CaseClass, y: CaseClass) => scoreCaseClass(x, y)
      case _ => 1.0

    }

    // if tree is a node, recursively travers children. If it is a leaf, just return the score
    // we process a geometrical mean
    tree.children.foldLeft(score)((acc, child) => acc * computeScore(child))
  }

  /**
    * Compare only the MatchCases conditions
    *
    * @return
    */
  def scoreMatchExpr(x: MatchExpr, y: MatchExpr): Double = {
    def scoreMatchCase(casesA: Seq[MatchCase], casesB: Seq[MatchCase]): Double = {
      val mapCasesA = toMap(casesA)
      val mapCasesB = toMap(casesB)
      scoreMapMatchCase(mapCasesA, mapCasesB)
    }

    /**
      * Compare the map containing the MatchCases
      * NOW: just check how many similar key they have
      * NEXT: take into account the order; some MatchCase can be non exclusive, meaning that it "eats" the next one:
      * case x if x < 4 => ...
      * case x if x < 10 => ...
      * doesn't have the same meaning if inverted.
      *
      * NEXT: take into account invoked expression
      *
      * @param mapCasesA
      * @param mapCasesB
      * @return
      */
    def scoreMapMatchCase(mapCasesA: Map[Tree, Expr], mapCasesB: Map[Tree, Expr]): Double = {
      val all = mapCasesA.keys.size + mapCasesB.keys.size.toDouble
      val diff = ((mapCasesA.keySet -- mapCasesB.keySet) ++ (mapCasesB.keySet -- mapCasesA.keySet)).size.toDouble
      (all - diff) / all
    }

    def toMap(cases: Seq[MatchCase]) = {
      cases.map(a => a.pattern match {
        case InstanceOfPattern(_, ct) => ct -> a.rhs
        case CaseClassPattern(_, ct, _) => ct -> a.rhs
        case _ => a.pattern -> a.rhs
      }).toMap
    }

    scoreMatchCase(x.cases, y.cases)
  }


  /**
    * One hard piece is to compare two case clase, because it cannot be normalized like value
    *
    * @return
    */

  def scoreClassDef(classA: ClassDef, classB: ClassDef): Double = {
    (classA, classB) match {
      case (a, b) if (a.isAbstract && b.isAbstract) =>
        if (a.knownCCDescendants.size == b.knownCCDescendants.size) 1.0
        else 0.0
      case (a: CaseClassDef, b: CaseClassDef) =>
        scoreCaseClassDef(a, b)
      case _ => 0.0

    }
  }

  def compareTypeTree(typeA: TypeTree, typeB: TypeTree): Double = (typeA, typeB) match {
    case (a: ClassType, b: ClassType) => scoreClassDef(a.classDef, b.classDef)
    case _ => 0.0
  }

  def scoreCaseClass(a: CaseClass, b: CaseClass): Double = {
    scoreCaseClassDef(a.ct.classDef, b.ct.classDef)
  }


  /**
    * Compare two CaseClass definition taking into account different parameter:
    * - the number of arguments of it's own type
    * - the number of arguments of it's parent type
    * - the other arguments of primitive types
    *
    * NEXT: take into account matching between parents
    * NEXT: take into account others parameters ?
    *
    * @param a
    * @param b
    * @return
    */
  def scoreCaseClassDef(a: CaseClassDef, b: CaseClassDef): Double = {
    val ownTypeA: Int = argumentsOfOwnType(a)
    val ownTypeB: Int = argumentsOfOwnType(b)
    val scoreOwnType = percent(ownTypeA, ownTypeB)

    val parentTypeA: Int = argumentsOfParentType(a)
    val parentTypeB: Int = argumentsOfParentType(b)
    val scoreParentType = percent(parentTypeA, parentTypeB)

    val otherTypeA = a.fields.map(_.getType).filterNot(_.isInstanceOf[ClassDef])
    val otherTypeB = b.fields.map(_.getType).filterNot(_.isInstanceOf[ClassDef])
    val scoreOtherType = scoreSeqType(otherTypeA, otherTypeB)

    // arithmetic mean instead of geometric, we don't want to have 0.0% if one of these criteria don't match
    val score: Double = mean(List(scoreOwnType, scoreParentType, scoreOtherType))

    score
  }


  def scoreSeqType(a: Seq[TypeTree], b: Seq[TypeTree]): Double = {
    val intersect = a.intersect(b).size
    matchScore(intersect, a.size, b.size)
  }

  /**
    * Count how many occurrences of its own type appear in its arguments
    * (to be improved if multiples types)
    *
    * @param a the case class
    * @return
    */
  def argumentsOfOwnType(a: CaseClassDef): Int =
    a.fields.map(_.getType).count(a.tparams.map(_.tp.getType).contains(_))


  /**
    * Count how many occurrences of its parent type appear in its arguments
    *
    * @param a
    * @return
    */
  def argumentsOfParentType(a: CaseClassDef): Int = a match {
    case _ if a.hasParent => a.fields.map(_.getType).count(_ == a.parent.get.getType)
    case _ => 0
  }


}
