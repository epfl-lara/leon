package leon
package synthesis.stoch

import purescala.Definitions.Program
import purescala.Expressions.Expr
import purescala.ExprOps._
import purescala.Types.StringType
import purescala.Types.TypeTree

object Statistics {

  // All sub-expressions
  def allSubExprs(expr: Expr): Seq[Expr] = collectPreorder{ e => List(e) }(expr)

  def allSubExprs(ctx: LeonContext, p: Program): Seq[Expr] = {
    for {
      unit <- p.units
      f <- unit.definedFunctions if ctx.files.contains(f.getPos.file)
      e <- allSubExprs(f.fullBody)
    } yield e
  }

  def allSubExprsByType(ctx: LeonContext, p: Program): Map[TypeTree, Seq[Expr]] = {
    allSubExprs(ctx, p).groupBy(_.getType)
  }

  // Expression constructor statistics
  type ExprConstrStats = Map[TypeTree, Map[Class[_ <: Expr], Int]]

  def ++(stats1: ExprConstrStats, stats2: ExprConstrStats): ExprConstrStats = {
    def addMaps[K](map1: Map[K, Int], map2: Map[K, Int]): Map[K, Int] = {
      map1 ++ map2.map{ case (k, v) => k -> (map1.getOrElse(k, 0) + v) }
    }

    stats1 ++ stats2.map{ case (k1, k2v) => k1 -> (addMaps(stats1.getOrElse(k1, Map()), k2v)) }
  }

  def exprConstrStatsToString(stats: ExprConstrStats): String = {
    val ans = new StringBuilder()
    def total[K](map: Map[K, Int]): Int = map.values.fold(0)(_ + _)
    for (typeConstrs <- stats.toList.sortBy(typeExpr => -total(typeExpr._2))) {
      val typeTotal = total(typeConstrs._2)
      for (constr <- typeConstrs._2.toList.sortBy(-_._2)) {
        ans.append(s"${typeConstrs._1}, ${typeTotal}, ${constr._1}, ${constr._2}\n")
      }
    }
    ans.toString()
  }

  def getExprConstrStats(ctx: LeonContext, p: Program): ExprConstrStats = {
    val asebt: Map[TypeTree, Seq[Expr]] = allSubExprsByType(ctx, p)
    val getExprType: Expr => Class[_ <: Expr] = _.getClass 
    val asecbt: Map[TypeTree, Seq[Class[_ <: Expr]]] = asebt.mapValues(_.map(getExprType))
    asecbt.mapValues(_.groupBy(identity).mapValues(_.size))
  }

  def getExprConstrStatsPretty(ctx: LeonContext, p: Program): String = {
    exprConstrStatsToString(getExprConstrStats(ctx, p))
  }

  // Type statistics
  def getTypeStats(ctx: LeonContext, p: Program): Map[TypeTree, Int] = {
    allSubExprs(ctx, p).groupBy(_.getType).mapValues(_.size)
  }

  def getTypeStatsPretty(ctx: LeonContext, p: Program): String = {
    val ans = new StringBuilder()
    for (typeFreq <- getTypeStats(ctx, p).toList.sortBy(-_._2)) {
      ans.append(s"${typeFreq._1} -> ${typeFreq._2}\n")
    }
    ans.toString()
  }

}