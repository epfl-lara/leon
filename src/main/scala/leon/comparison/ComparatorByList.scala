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
    * Flat an Expression tree into a list using different method according with type of expression
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
    case And(exprs) => List(expr) ++ exprs.flatMap(treeToList(_))
    case Or(exprs) => List(expr) ++ exprs.flatMap(treeToList(_))
    case Implies(lhs, rhs) => List(expr) ++ treeToList(lhs) ++ treeToList(rhs)
    case Not(internalExpr) => List(expr) ++ treeToList(internalExpr)
    case IsInstanceOf(internExpr, _) => List(expr) ++ treeToList(internExpr)
    case AsInstanceOf(internExpr, _) => List(expr) ++ treeToList(internExpr)

    // Petite pause au string, je vais reprendre demain

    // default value for any easy-to-handled or Terminal expression
    // including: NoTree, Error, Variable, MethodInvocation, This, all Literal, ConverterToString
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
