package leon.comparison

import leon.purescala.ExprOps
import leon.purescala.Expressions.{CaseClassPattern, _}

/**
  * Created by joachimmuth on 25.04.16.
  *
  * The idea here is a little more elaborated, and is based of recursive search crawling the expression tree and
  * comparing two expression. Each type of expression have its own method.
  */
object ComparatorByTree {


  def compare(expr_base: Expr, expr: Expr): Double = {
    val expr_base_norm = ExprOps.normalizeStructure(expr_base)._1
    val expr_norm = ExprOps.normalizeStructure(expr)._1

    compareExpr(expr_base_norm, expr_norm)
  }


  def compareExpr(expr_base: Expr, expr: Expr): Double = (expr_base, expr) match{
    case (_,_) if (expr_base == expr) => 1.0
    case (MatchExpr(scrutinee_b, cases_b), MatchExpr(scrutinee, cases)) => compareMatchExpr(cases_b, cases)
    case (Let(binderA, valueA, bodyA), Let(binder, value, body)) => 10.0
    case (_,_) => {
      println("TYPE OF EXPRESSION")
      println(expr)
      println("type", expr.getType)
      println("class", expr.getClass)
      println("class.type", expr.getType.getClass)
      0.0
    }

  }


  /**
    * compare only the MatchCases conditions, note the returned value, which are compared through main compareExp
    * function
    *
    * @return
    */
  def compareMatchExpr(casesB: Seq[MatchCase], cases: Seq[MatchCase]): Double = {
    val mapCasesB = toMap(casesB)
    val mapCases = toMap(cases)
    0.1
  }

  def toMap(cases: Seq[MatchCase]) = {
    cases.map(a => a.pattern match {
      case InstanceOfPattern(_, ct) => (ct.classDef -> a.rhs)
      case CaseClassPattern(_, ct, _) => (ct.classDef -> a.rhs)
      case _ => (a.pattern -> a.rhs)
    }).toMap
  }
}
