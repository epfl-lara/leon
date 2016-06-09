package leon.comparison

import leon.purescala.Definitions.FunDef
import leon.purescala.Expressions._
import leon.comparison.Utils._
import leon.comparison.Scores._

/**
  * Created by joachimmuth on 08.06.16.
  *
  * Consider a holed function and try to find the best match (if there is some!) between this and one of the function
  * existing in the corpus.
  *
  * To do so, we use a similar method as ComparatorDirectScoreTree were we create all possible common tree shared by
  * two functions. As ComparatorDirectScoreTree creates pair of expression based on their score, we only need to do a
  * little modification in order to consider the Hole as a possible match, based on their type.
  * We choose then the function with the common tree having the higher score.
  *
  * We use this corpus function to fill the hole, and we replace the hole by the matching expression in the common tree.
  *
  * We return the holed function, the corpus function used to complete it, and the completed function (if there is some).
  *
  * IMPORTANT: at the moment the object if implemented to handle one and only one hole
  */
object Completor {

  case class Suggestion(expr: Option[Expr])


  def suggestCompletion(funDef: FunDef, corpus: ComparisonCorpus): (FunDef, Option[FunDef], Option[Expr]) = {
    val expr = funDef.body.get

    // for each function of corpus, search all roots of common tree that include the hole
    val funDefAndRoots = corpus.funDefs map (f => (f, possibleRoots(f, expr)))

    // for each function of corpus, search all common tree respective to these roots
    // (filter only the ones containing the hole)
    val funDefAndTrees = funDefAndRoots map { p =>
      (p._1, p._2 flatMap ComparatorDirectScoreTree.possibleTrees filter hasHole)
    }

    // if no function match, return None
    if (funDefAndTrees.isEmpty)
      return (funDef, None, None)

    val suggestion = selectBestSuggestion(funDefAndTrees)

    suggestion match {
      case None => (funDef, None, None)
      case Some(pair) => (funDef, Some(pair._1), Some(fillHole(expr, pair._2)))
    }
  }



  def possibleRoots(funDef_corpus: FunDef, expr: Expr): List[Value] =
    ComparatorDirectScoreTree.possibleRoots(funDef_corpus.body.get, expr) filter (e => Utils.hasHole(e.b))

  def getBody(funDef: FunDef): Expr = funDef.body.get

  def hasHole(tree: myTree[Value]): Boolean = {
    tree.toList map (p => p.b) exists (e => e.isInstanceOf[Choose])
  }

  def scoreOptionTree(tree: Option[myTree[Value]]): Double = tree match {
    case None => 0.0
    case Some(t) => ComparatorDirectScoreTree.geometricMean(t)
  }


  /**
    * select the best suggestion to fill the hole i.e. the common tree having the higher score between all the common
    * trees and all the function of corpus
    *
    * @param funDefAndTrees
    * @return
    */
  def selectBestSuggestion(funDefAndTrees: List[(FunDef, List[myTree[Value]])]):
  Option[(FunDef, Expr)] = {
    val funDefAndBestTree = funDefAndTrees map { p =>
      (p._1, selectBestTree(p._2))
    }

    selectBestFun(funDefAndBestTree) match {
      case None => None
      case Some(pair) => Some(pair._1, findPairOfTheHole(pair._2))
    }
  }

  def selectBestTree(list: List[myTree[Value]]): Option[myTree[Value]] = list match {
    case Nil => None
    //case x::xs => Some(list.sortBy(t => -ComparatorDirectScoreTree.scoreTree(t)).head)
    case x :: xs => Some(list.sortBy(-_.size).head)
  }

  def selectBestFun(list: List[(FunDef, Option[myTree[Value]])]): Option[(FunDef, myTree[Value])] = {
    val (bestFun, bestTree) = (list sortBy (p => -scoreOptionTree(p._2))).head

    bestTree match {
      case Some(tree) => Some(bestFun, tree)
      case None => None
    }
  }

  /**
    * Find in common tree the value that paired the hole and the expression from the corpus. The hole will be filled
    * with this hole
    *
    * @param tree
    * @return
    */
  def findPairOfTheHole(tree: myTree[Value]): Expr =
    (tree.toList filter (p => p.b.isInstanceOf[Choose])).head.a

  /**
    * Really really ugly function used to travers recursively the tree until finding the hole and replace it by
    * the wished expression.
    *
    * see "case Choose(_) => ..."
    *
    * Probably a better way to perform it, using pre-existing function that I didn't know.
    *
    * @param exprToFill
    * @param corpus
    * @return
    */
  def fillHole(exprToFill: Expr, corpus: Expr): Expr = {
    def fill(expr: Expr): Expr = expr match {
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
        MatchExpr(fill(scrutinee), cases map { c =>
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
      case RealMinus(lhs, rhs) =>
        RealMinus(fill(lhs), fill(rhs))
      case RealDivision(lhs, rhs) =>
        RealDivision(fill(lhs), fill(rhs))
      case RealTimes(lhs, rhs) =>
        RealTimes(fill(lhs), fill(rhs))
      case RealUMinus(argExpr) =>
        RealUMinus(fill(argExpr))

      /* Tuple operations */
      case Tuple(exprs) => Tuple(exprs map fill)
      case TupleSelect(tuple, index) =>
        TupleSelect(fill(tuple), index)

      /* Set operations */
      case FiniteSet(elements, base) => FiniteSet(elements map fill, base)
      case ElementOfSet(element, set) =>
        ElementOfSet(fill(element), fill(set))
      case SetCardinality(set) => SetCardinality(fill(set))
      case SubsetOf(set1, set2) => SubsetOf(fill(set1), fill(set2))
      case SetIntersection(set1, set2) =>
        SetIntersection(fill(set1), fill(set2))
      case SetUnion(set1, set2) =>
        SetUnion(fill(set1), fill(set2))
      case SetDifference(set1, set2) =>
        SetDifference(fill(set1), fill(set2))

      /* Map operations */
      /*not handled for the moment*/
      case FiniteMap(pairs, keyType, valueType) =>
        FiniteMap(pairs, keyType, valueType)
      case MapApply(map, key) => MapApply(fill(map), fill(key))
      case MapUnion(map1, map2) => MapUnion(fill(map1), fill(map2))
      case MapDifference(map, keys) => MapDifference(fill(map), fill(keys))
      case MapIsDefinedAt(map, key) => MapIsDefinedAt(fill(map), fill(key))

      /* Array operations */
      case ArraySelect(array, index) => ArraySelect(fill(array), fill(index))
      case ArrayUpdated(array, index, newValue) =>
        ArrayUpdated(fill(array), fill(index), fill(newValue))
      case ArrayLength(array) => ArrayLength(fill(array))
      /*not handled for the moment*/
      case NonemptyArray(elems, defaultLength) =>
        NonemptyArray(elems, defaultLength)
      case EmptyArray(tpe) => EmptyArray(tpe)

      /* Holes */
      case Choose(pred) => corpus
      //case Hole(_, alts) => onParent(expr) ++ alts.flatMap(onChild(_))


      // default value for any easy-to-handled or Terminal expression
      // including: NoTree, Error, Variable, MethodInvocation, This, all Literal, ConverterToString
      // leave aside (at least for the moment): String Theory, BitVector Operation, Special trees for synthesis (holes, ...)
      case x => x
    }

    fill(exprToFill)
  }


}
