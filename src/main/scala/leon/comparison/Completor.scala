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
    val expr = funDef.body.get
    val exprsCorpus = corpus.funDefs map(_.body.get)

    // for each function of corpus, search all roots of common tree
    val funDefAndRoots = corpus.funDefs map(f => (f, possibleRoots(f, expr)))
    println("------funDefAndRoots--------")
    funDefAndRoots map println
    println("----------------------------")

    println("------possibleTrees--------")
    funDefAndRoots.head._2 flatMap possibleTrees map println
    println("----------------------------")

    println("------hasHole--------")
    funDefAndRoots.head._2 flatMap possibleTrees filter hasHole map println
    println("----------------------------")


    // for each function of corpus, search all common tree respective to these roots
    // (filter only the ones containing the hole)
    val funDefAndTrees = funDefAndRoots map {p =>
      (p._1, p._2 flatMap possibleTrees filter hasHole)
    }

    println("------funDefAndTrees--------")
    funDefAndTrees map println
    println("----------------------------")

    if (funDefAndTrees.isEmpty)
      return (funDef, None, None)

    val suggestion = chooseBestSuggestion(funDefAndTrees)


    println("------suggestion--------")
    println(suggestion)
    println("----------------------------")


    suggestion match {
      case None => (funDef, None, None)
      case Some(pair) => (funDef, Some(pair._1), Some(fillHole(expr, pair._2)))
    }
  }



  def possibleRoots(funDef_corpus: FunDef, expr: Expr): List[(Expr, Expr, Double)] =
    ComparatorDirectScoreTree.possibleRoots(funDef_corpus.body.get, expr) filter (e => Utils.hasHole(e._2))

  def getBody(funDef: FunDef): Expr = funDef.body.get

  def hasHole(tree: myTree[(Expr, Expr, Double)]): Boolean = {
    tree.toList map(p => p._2) exists (e => e.isInstanceOf[Choose])
  }



  def chooseBestSuggestion(funDefAndTrees: List[(FunDef, List[myTree[(Expr, Expr, Double)]])]):
  Option[(FunDef, Expr)] = {
    val funDefAndBestTree = funDefAndTrees map { p =>
      (p._1, selectBestTree(p._2))
    }

    println("--------funDefAndBestTree----------")
    println(funDefAndBestTree)
    println("------------------------------------")

    selectBestFun(funDefAndBestTree) match {
      case None => None
      case Some(pair) => Some(pair._1, findPairOfTheHole(pair._2))
    }
  }

  def findPairOfTheHole(tree: myTree[(Expr, Expr, Double)]): Expr =
    (tree.toList filter (p => p._2.isInstanceOf[Choose])).head._1


  def selectBestTree(list: List[myTree[(Expr, Expr, Double)]]): Option[myTree[(Expr, Expr, Double)]] = list match{
    case Nil => None
    //case x::xs => Some(list.sortBy(t => -ComparatorDirectScoreTree.scoreTree(t)).head)
    case x::xs => Some(list.sortBy(-_.size).head)
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



  def fillHole(expr: Expr, corpus: Expr): Expr = {
    def fill(expr: Expr): Expr = {
      case Require(pred, body) => Require(fill(pred), fill(body))
      case Ensuring(body, pred) => Ensuring(fill(body), fill(pred))
      case Assert(pred, error, body) => Assert(fill(pred), error, fill(body))
      case Let(binder, value, body) => Let(binder, fill(value), fill(body))

      // how to handle fds (function definition) ??
      case LetDef(fds, body) => LetDef(fds, fill(body))

      case Application(callee, args) => Application(fill(callee), args map fill)
      case Lambda(args, body) => Lambda(args, fill(body))
      case Forall(args, body) => Forall(args, fill(body))
      case FunctionInvocation(tfd, args) =>
        FunctionInvocation(tfd, args map fill)
      case IfExpr(cond, thenn, elze) => IfExpr(fill(cond), fill(thenn), fill(elze))

      // we don't list the scrutinee
      // method cases.expression return both optGuard and rhs
      case MatchExpr(scrutinee, cases) =>
        MatchExpr(fill(scrutinee), cases map{ c =>
          MatchCase(c.pattern, c.optGuard, fill(c.rhs))
        })

      case CaseClass(ct, args) => CaseClass(ct, args map fill)
      case CaseClassSelector(classType, caseClass, selector) =>
        CaseClassSelector(classType, fill(caseClass), selector)
      case Equals(lhs, rhs) =>
        Equals(fill(lhs), fill(rhs))

      /* Propositional logic */
      case And(exprs) =>
        And(exprs map fill)
      case Or(exprs) =>
        Or(exprs map fill)
      case Implies(lhs, rhs) =>
        Implies(fill(lhs), fill(rhs))
      case Not(argExpr) =>
        Not(fill(argExpr))

      case IsInstanceOf(argExpr, classType) =>
        IsInstanceOf(fill(argExpr), classType)
      case AsInstanceOf(argExpr, tpe) =>
        AsInstanceOf(fill(argExpr), tpe)

      /* Integer arithmetic */
      case Plus(lhs, rhs) => Plus(fill(lhs), fill(rhs))
      case Minus(lhs, rhs) =>
        Minus(fill(lhs), fill(rhs))
      case UMinus(argExpr) =>
        UMinus(fill(argExpr))
      case Times(lhs, rhs) =>
        Times(fill(lhs), fill(rhs))
      case Division(lhs, rhs) =>
        Division(fill(lhs), fill(rhs))
      case Remainder(lhs, rhs) =>
        Remainder(fill(lhs), fill(rhs))
      case Modulo(lhs, rhs) =>
        Modulo(fill(lhs), fill(rhs))
      case GreaterThan(lhs, rhs) =>
        GreaterThan(fill(lhs), fill(rhs))
      case GreaterEquals(lhs, rhs) =>
        GreaterEquals(fill(lhs), fill(rhs))
      case LessThan(lhs, rhs) =>
        LessThan(fill(lhs), fill(rhs))
      case LessEquals(lhs, rhs) =>
        LessEquals(fill(lhs), fill(rhs))

      /* Real arithmetic */
      case RealPlus(lhs, rhs) =>
        RealPlus(fill(lhs), fill(rhs))
      case RealMinus(lhs, rhs) => onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
      case RealDivision(lhs, rhs) =>
        onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
      case RealTimes(lhs, rhs) => onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
      case RealUMinus(argExpr) =>
        onParent(expr) ++ onChild(argExpr)

      /* Tuple operations */
      case Tuple(exprs) => onParent(expr) ++ exprs.flatMap(onChild(_))
      case TupleSelect(tuple, _) =>
        onParent(expr) ++ onChild(tuple)

      /* Set operations */
      case FiniteSet(elements, _) => onParent(expr) ++ elements.flatMap(onChild(_))
      case ElementOfSet(element, set) =>
        onParent(expr) ++ onChild(element) ++ onChild(set)
      case SetCardinality(set) => onParent(expr) ++ onChild(set)
      case SubsetOf(set1, set2) => onParent(expr) ++ onChild(set1) ++ onChild(set2)
      case SetIntersection(set1, set2) =>
        onParent(expr) ++ onChild(set1) ++ onChild(set2)
      case SetUnion(set1, set2) =>
        onParent(expr) ++ onChild(set1) ++ onChild(set2)
      case SetDifference(set1, set2) => onParent(expr) ++ onChild(set1) ++ onChild(set2)

      /* Map operations */
      case FiniteMap(pairs, _, _) =>
        onParent(expr) ++ pairs.toList.flatMap(t => onChild(t._1) ++ onChild(t._2))
      case MapApply(map, key) => onParent(expr) ++ onChild(map) ++ onChild(key)
      case MapUnion(map1, map2) => onParent(expr) ++ onChild(map1) ++ onChild(map2)
      case MapDifference(map, keys) => onParent(expr) ++ onChild(map) ++ onChild(keys)
      case MapIsDefinedAt(map, key) => onParent(expr) ++ onChild(map) ++ onChild(key)

      /* Array operations */
      case ArraySelect(array, index) => onParent(expr) ++ onChild(array) ++ onChild(index)
      case ArrayUpdated(array, index, newValue) =>
        onParent(expr) ++ onChild(array) ++ onChild(index) ++ onChild(newValue)
      case ArrayLength(array) => onParent(expr) ++ onChild(array)
      case NonemptyArray(elems, defaultLength) => onParent(expr) ++ elems.flatMap(t => onChild(t._2))
      case EmptyArray(_) => onParent(expr)

      /* Holes */
      case Choose(pred) => onParent(expr)
      //case Hole(_, alts) => onParent(expr) ++ alts.flatMap(onChild(_))


      // default value for any easy-to-handled or Terminal expression
      // including: NoTree, Error, Variable, MethodInvocation, This, all Literal, ConverterToString
      // leave aside (at least for the moment): String Theory, BitVector Operation, Special trees for synthesis (holes, ...)
      case x if x.isInstanceOf[Expr] => onParent(expr)

      //default value for error handling, should never reach that
      case _ => Nil
    }

  }








}
