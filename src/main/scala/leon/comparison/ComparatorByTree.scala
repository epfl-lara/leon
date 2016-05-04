package leon.comparison

import leon.purescala.ExprOps
import leon.purescala.Expressions.{CaseClassPattern, _}
import leon.comparison.Utils._
import leon.purescala.Common.Tree
/**
  * Created by joachimmuth on 25.04.16.
  *
  * The idea here is a little more elaborated, and is based of recursive search crawling the expression tree and
  * comparing two expression. Each type of expression have its own method.
  */
object ComparatorByTree extends Comparator {
  val name = "byTree"


  def compare(expr_base: Expr, expr: Expr): Double = {
    val expr_base_norm = ExprOps.normalizeStructure(expr_base)._1
    val expr_norm = ExprOps.normalizeStructure(expr)._1

    compareExpr(expr_base_norm, expr_norm)
  }


  def compareExpr(expr_base: Expr, expr: Expr): Double = (expr_base, expr) match{
    case (_,_) if (expr_base == expr) => 1.0
    case (MatchExpr(scrutinee_b, cases_b), MatchExpr(scrutinee, cases)) => compareMatchExpr(cases_b, cases)
    case (Let(binderB, valueB, bodyB), Let(binder, value, body)) =>
      mean(compareExpr(valueB, value), compareExpr(bodyB, body))
    case (CaseClass(ct_b, args_b), CaseClass(ct, args)) =>
      mean(compareCaseClassDef(ct_b.classDef, ct.classDef))

    case (_,_) => 0.0

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
    compareMap(mapCasesB, mapCases)
  }

  /**
    * Compare the map containing the MatchCases
    * NOW: just check how many similar key they have
    * NEXT: do a mean between the pattern AND the result and iterate on the result expression
    *
    * @param mapCasesB
    * @param mapCases
    * @return
    */
  def compareMap(mapCasesB: Map[Tree, Expr], mapCases: Map[Tree, Expr]): Double = {
    val all = mapCasesB.keys.size + mapCases.keys.size.toDouble
    val diff = ((mapCasesB.keySet -- mapCases.keySet) ++ (mapCases.keySet -- mapCasesB.keySet)).size.toDouble
    (all - diff) / all
  }

  def toMap(cases: Seq[MatchCase]) = {
    cases.map(a => a.pattern match {
      case InstanceOfPattern(_, ct) => (ct -> a.rhs)
      case CaseClassPattern(_, ct, _) => (ct -> a.rhs)
      case _ => (a.pattern -> a.rhs)
    }).toMap
  }
}
