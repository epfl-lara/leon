package leon.comparison

import leon.purescala.ExprOps
import leon.purescala.Expressions.{CaseClassPattern, _}

/**
  * Created by joachimmuth on 25.04.16.
  *
  * This way of basic comparison flat both functional tree into lists and compare them in every possible combination.
  *
  * The easy-to-understand way of working provide a point of comparison for further advanced method.
  */
object ComparatorByList {
  val print = false

  /**
    * Compare two functions using different method
    *
    * @param expr_base
    * @param expr
    * @return
    */
  def compare(expr_base: Expr, expr: Expr): Double = {
    val listExpr_base = treeToList(expr_base)
    val listExpr = treeToList(expr)

    val similarExprList = for{
      expr_base <- listExpr_base
      expr <- listExpr
      if (compareExpr(expr_base, expr))
    } yield {
      (expr_base, expr)
    }

    val percentageSimilarity =
      math.min((similarExprList.size.toDouble / listExpr_base.size.toDouble),
        (similarExprList.size.toDouble / listExpr.size.toDouble)
      )

    percentageSimilarity
  }

  /**
    * Flat an Expression tree into a list
    * Put the current Expr into a list and recursively call the function over all its arguments of type Expr.
    *
    * @param expr
    * @return
    */
  def treeToList(expr: Expr): List[Expr] = expr match {
    case Require(pred, body) => List(expr) ++ treeToList(pred) ++ treeToList(body)
    case Ensuring(body, pred) => List(expr) ++ treeToList(body) ++ treeToList(pred)
    case Assert(pred, _, body) => List(expr) ++ treeToList(pred) ++ treeToList(body)
    case Let(binder, value, body) => List(expr) ++ treeToList(value) ++ treeToList(body)

    // how to handle fds (function definition) ??
    case LetDef(fds, body) => List(expr) ++ treeToList(body)

    case Application(callee, args) => List(expr) ++ treeToList(callee) ++ args.flatMap(treeToList(_))
    case Lambda(_, body) => List(expr) ++ treeToList(expr)
    case Forall(_, body) => List(expr) ++ treeToList(body)
    case FunctionInvocation(_ ,args) => List(expr) ++ args.flatMap(treeToList(_))
    case IfExpr(cond, thenn, elze) => List(expr) ++ treeToList(cond) ++ treeToList(thenn) ++ treeToList(elze)

    // we don't list the scrutinee
    // method cases.expression return both optGuard and rhs
    case MatchExpr(scrutinee, cases) =>
      List (expr)  ++ cases.flatMap(m => m.expressions.flatMap(e => treeToList(e)))

    case CaseClass(_, args) => List(expr) ++ args.flatMap(treeToList(_))
    case CaseClassSelector(_, caseClass, _) => List(expr) ++ treeToList(caseClass)
    case Equals(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)

    /* Propositional logic */
    case And(exprs) => List(expr) ++ exprs.flatMap(treeToList(_))
    case Or(exprs) => List(expr) ++ exprs.flatMap(treeToList(_))
    case Implies(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case Not(argExpr) => List(expr) ++ treeToList(argExpr)

    case IsInstanceOf(argExpr, _) => List(expr) ++ treeToList(argExpr)
    case AsInstanceOf(argExpr, _) => List(expr) ++ treeToList(argExpr)

    /* Integer arithmetic */
    case Plus(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case Minus(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case UMinus(argExpr) => List(expr) ++ treeToList(argExpr)
    case Times(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case Division(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case Remainder(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case Modulo(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case GreaterThan(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case GreaterEquals(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case LessThan(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case LessEquals(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)

    /* Real arithmetic */
    case RealPlus(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case RealMinus(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case RealDivision(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case RealTimes(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case RealUMinus(argExpr) => List(expr) ++ treeToList(argExpr)

    /* Tuple operations */
    case Tuple(exprs) => List(expr) ++ exprs.flatMap(treeToList(_))
    case TupleSelect(tuple, _) => List(expr) ++ treeToList(tuple)

    /* Set operations */
    case FiniteSet(elements, _ ) => List(expr) ++ elements.flatMap(treeToList(_))
    case ElementOfSet(element, set) => List(expr) ++ treeToList(element) ++ treeToList(set)
    case SetCardinality(set) => List(expr) ++ treeToList(set)
    case SubsetOf(set1, set2) => List(expr) ++ treeToList(set1) ++ treeToList(set2)
    case SetIntersection(set1, set2) => List(expr) ++ treeToList(set1) ++ treeToList(set2)
    case SetUnion(set1, set2) => List(expr) ++ treeToList(set1) ++ treeToList(set2)
    case SetDifference(set1, set2) => List(expr) ++ treeToList(set1) ++ treeToList(set2)

    /* Map operations */
    case FiniteMap(pairs, _, _) => List(expr) ++ pairs.toList.flatMap(t => treeToList(t._1) ++ treeToList(t._2))
    case MapApply(map, key) => List(expr) ++ treeToList(map) ++ treeToList(key)
    case MapUnion(map1, map2) => List(expr) ++ treeToList(map1) ++ treeToList(map2)
    case MapDifference(map, keys) => List(expr) ++ treeToList(map) ++ treeToList(keys)
    case MapIsDefinedAt(map, key) => List(expr) ++ treeToList(map) ++ treeToList(key)

    /* Array operations */
    case ArraySelect(array, index) => List(expr) ++ treeToList(array) ++ treeToList(index)
    case ArrayUpdated(array, index, newValue) => List(expr) ++ treeToList(array) ++ treeToList(index) ++ treeToList(newValue)
    case ArrayLength(array) => List(expr) ++ treeToList(array)
    case NonemptyArray(elems, defaultLength) => List(expr) ++ elems.flatMap(t => treeToList(t._2))
    case EmptyArray(_) => List(expr)







    // default value for any easy-to-handled or Terminal expression
    // including: NoTree, Error, Variable, MethodInvocation, This, all Literal, ConverterToString
    // leave aside (at least for the moment): String Theory, BitVector Operation, Special trees for synthesis (holes, ...)
    case x if x.isInstanceOf[Expr] => List(x)

    //default value for error handling, should never reach that
    case _ => Nil
  }

  /**
    * Extract a map from a PatternMatch function (match...case) in order to be comparable without caring about the
    * order
    * (waring: this comparison make sense only if the MatchCases are exclusives)
    *
    * e.g : list match {
    *   case x::y::xs => foo(x, y) ++ recursion(xs)
    *   case x::xs => Nil
    *   }
    *
    * is not equal to:
    *
    *   list match {
    *   case x::xs => Nil
    *   case x::y::xs => foo(x, y) ++ recursion(xs)
    *   }
    *
    * @param cases_base
    * @return
    */
  def extractPatternMatchMap(cases_base: Seq[MatchCase]) = {
    cases_base.map(a => a.pattern match {
      case InstanceOfPattern(_, ct) => (ct.classDef -> a.rhs)
      case CaseClassPattern(_, ct, _) => {
        println(a)
        (ct.classDef -> a.rhs)
      }
      case _ => (a.pattern -> a.rhs)
    }).toMap
  }


  def extractValueMatchMap(cases_base: Seq[MatchCase]) = {
    cases_base.map(a => a.pattern -> a.rhs).toMap
  }

  // IDEE: comparer les types plutôt que les pattern complet des match case, et éventuellement oublié les optGuard
  def compareExpr(expr_base: Expr, expr: Expr): Boolean = {
    val expr_base_norm = ExprOps.normalizeStructure(expr_base)._1
    val expr_norm = ExprOps.normalizeStructure(expr)._1

    (expr_base_norm, expr_norm) match {
      case (MatchExpr(_, cases_base), MatchExpr(_, cases)) =>
        val map_case_base = extractPatternMatchMap(cases_base)
        val map_case = extractPatternMatchMap(cases)
        map_case_base == map_case

      case _ =>
        expr_base_norm == expr_norm
    }
  }

}
