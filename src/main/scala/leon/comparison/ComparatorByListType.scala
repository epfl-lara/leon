package leon.comparison

import leon.purescala.Expressions._
import leon.comparison.Utils._

/**
  * Created by joachimmuth on 02.05.16.
  *
  * This method shares similarities with the ComparatorByList.
  * We kkep the idea of comparing a list of expressions (disregarding their order), but now, instead of comparing
  * two expressions (i.e. tree) we will extract the type of each expression.
  *
  * x match {
  *   case 1 => 'a'
  *   case 2 => 'b'
  * }
  *
  * ComparatorByList -> {complete match, leaf(a), leaf(b)}
  * ComparatorByListType -> {node(match), leaf(a), leaf(b)}
  *
  * x match {
  *   case 1 => 'a'
  *   case 2 => 'c'
  * }
  *
  * ComparatorByList -> similarity 33%
  * ComparatorByListType -> similarity 66%
  */
object ComparatorByListType extends Comparator {
  val name = "byListType"

  /**
    * Compare two functions using different method
    *
    * @param expr_base
    * @param expr
    * @return
    */
  def compare(expr_base: Expr, expr: Expr): Double = {
    val listClassesB = collectClass(expr_base)
    val listClasses = collectClass(expr)

    val test = treeToList(expr_base)
    println("are my function correct ? ", listClassesB == test)
    println(listClassesB)
    println(test)

    val similarExpr: Int = pairsOfSimilarExp(listClassesB, listClasses)

    Utils.percentBetweenTwo(similarExpr, listClassesB.size, listClasses.size)
  }


  def pairsOfSimilarExp(listExpr_base: List[Class[_ <: Expr]], listExpr: List[Class[_ <: Expr]]): Int = {
    def helper(listExpr_base: List[Class[_ <: Expr]], listExpr: List[Class[_ <: Expr]], acc: Int): Int =
      listExpr match {
        case Nil => acc
        case x::xs if listExpr_base.contains(x) => helper(listExpr_base diff List(x), xs, acc + 1)
        case x::xs => helper(listExpr_base, xs, acc)
      }

    helper(listExpr_base, listExpr, 0)
  }

  def treeToList(expr: Expr): List[Class[_ <: Expr]] = expr match {
    case Require(pred, body) => List(expr.getClass) ++ treeToList(pred) ++ treeToList(body)
    case Ensuring(body, pred) => List(expr.getClass) ++ treeToList(body) ++ treeToList(pred)
    case Assert(pred, _, body) => List(expr.getClass) ++ treeToList(pred) ++ treeToList(body)
    case Let(binder, value, body) => List(expr.getClass) ++ treeToList(value) ++ treeToList(body)

    // how to handle fds (function definition) ??
    case LetDef(fds, body) => List(expr.getClass) ++ treeToList(body)

    case Application(callee, args) => List(expr.getClass) ++ treeToList(callee) ++ args.flatMap(treeToList(_))
    case Lambda(_, body) => List(expr.getClass) ++ treeToList(expr)
    case Forall(_, body) => List(expr.getClass) ++ treeToList(body)
    case FunctionInvocation(_ ,args) => List(expr.getClass) ++ args.flatMap(treeToList(_))
    case IfExpr(cond, thenn, elze) => List(expr.getClass) ++ treeToList(cond) ++ treeToList(thenn) ++ treeToList(elze)

    // we don't list the scrutinee
    // method cases.expression return both optGuard and rhs
    case MatchExpr(scrutinee, cases) =>
      List(expr.getClass)  ++ cases.flatMap(m => m.expressions.flatMap(e => treeToList(e)))

    case CaseClass(_, args) => List(expr.getClass) ++ args.flatMap(treeToList(_))
    case CaseClassSelector(_, caseClass, _) => List(expr.getClass) ++ treeToList(caseClass)
    case Equals(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)

    /* Propositional logic */
    case And(exprs) => List(expr.getClass) ++ exprs.flatMap(treeToList(_))
    case Or(exprs) => List(expr.getClass) ++ exprs.flatMap(treeToList(_))
    case Implies(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case Not(argExpr) => List(expr.getClass) ++ treeToList(argExpr)

    case IsInstanceOf(argExpr, _) => List(expr.getClass) ++ treeToList(argExpr)
    case AsInstanceOf(argExpr, _) => List(expr.getClass) ++ treeToList(argExpr)

    /* Integer arithmetic */
    case Plus(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case Minus(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case UMinus(argExpr) => List(expr.getClass) ++ treeToList(argExpr)
    case Times(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case Division(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case Remainder(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case Modulo(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case GreaterThan(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case GreaterEquals(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case LessThan(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case LessEquals(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)

    /* Real arithmetic */
    case RealPlus(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case RealMinus(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case RealDivision(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case RealTimes(lhs, rhs) => List(expr.getClass) ++ treeToList(lhs) ++ treeToList(rhs)
    case RealUMinus(argExpr) => List(expr.getClass) ++ treeToList(argExpr)

    /* Tuple operations */
    case Tuple(exprs) => List(expr.getClass) ++ exprs.flatMap(treeToList(_))
    case TupleSelect(tuple, _) => List(expr.getClass) ++ treeToList(tuple)

    /* Set operations */
    case FiniteSet(elements, _ ) => List(expr.getClass) ++ elements.flatMap(treeToList(_))
    case ElementOfSet(element, set) => List(expr.getClass) ++ treeToList(element) ++ treeToList(set)
    case SetCardinality(set) => List(expr.getClass) ++ treeToList(set)
    case SubsetOf(set1, set2) => List(expr.getClass) ++ treeToList(set1) ++ treeToList(set2)
    case SetIntersection(set1, set2) => List(expr.getClass) ++ treeToList(set1) ++ treeToList(set2)
    case SetUnion(set1, set2) => List(expr.getClass) ++ treeToList(set1) ++ treeToList(set2)
    case SetDifference(set1, set2) => List(expr.getClass) ++ treeToList(set1) ++ treeToList(set2)

    /* Map operations */
    case FiniteMap(pairs, _, _) => List(expr.getClass) ++ pairs.toList.flatMap(t => treeToList(t._1) ++ treeToList(t._2))
    case MapApply(map, key) => List(expr.getClass) ++ treeToList(map) ++ treeToList(key)
    case MapUnion(map1, map2) => List(expr.getClass) ++ treeToList(map1) ++ treeToList(map2)
    case MapDifference(map, keys) => List(expr.getClass) ++ treeToList(map) ++ treeToList(keys)
    case MapIsDefinedAt(map, key) => List(expr.getClass) ++ treeToList(map) ++ treeToList(key)

    /* Array operations */
    case ArraySelect(array, index) => List(expr.getClass) ++ treeToList(array) ++ treeToList(index)
    case ArrayUpdated(array, index, newValue) => List(expr.getClass) ++ treeToList(array) ++ treeToList(index) ++ treeToList(newValue)
    case ArrayLength(array) => List(expr.getClass) ++ treeToList(array)
    case NonemptyArray(elems, defaultLength) => List(expr.getClass) ++ elems.flatMap(t => treeToList(t._2))
    case EmptyArray(_) => List(expr.getClass)




    // default value for any easy-to-handled or Terminal expression
    // including: NoTree, Error, Variable, MethodInvocation, This, all Literal, ConverterToString
    // leave aside (at least for the moment): String Theory, BitVector Operation, Special trees for synthesis (holes, ...)
    case x if x.isInstanceOf[Expr] => List(x.getClass)

    //default value for error handling, should never reach that
    case _ => Nil
  }

}
