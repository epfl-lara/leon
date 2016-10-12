package leon
package synthesis.stoch

import purescala.Definitions.Program
import purescala.Expressions.Expr
import purescala.ExprOps
import purescala.Types.StringType
import purescala.Types.TypeParameter
import purescala.Types.TypeTree
import purescala.TypeOps

object Statistics {

  // All sub-expressions
  def allSubExprs(expr: Expr): Seq[Expr] = ExprOps.collectPreorder{ e => List(e) }(expr)

  def allSubExprs(ctx: LeonContext, p: Program): Seq[Expr] = {
    for {
      unit <- p.units
      f <- unit.definedFunctions if ctx.files.contains(f.getPos.file)
      e <- allSubExprs(f.fullBody)
    } yield e
  }

  def allSubExprsByType(ctx: LeonContext, p: Program): Map[TypeTree, Seq[Expr]] = {
    val ans = allSubExprs(ctx, p).groupBy(_.getType)
    for (typeTree <- ans.keys) {
      println(s"${typeTree}: ${getTypeParams(typeTree)}")
    }
    ans
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

  // Type normalization
  // We assume that all type parameters are ordered: T, U, V, ...
  // Each type is converted into the lexicographically smallest type where equality / inequality constraints are
  // preserved between all type parameter occurrences.
  // For example:
  // 1. All base types are unchanged: BigInt ~~> BigInt, Unit ~~> Unit, String ~~> String, etc.
  // 2. All types which are individual occurrences of a type parameter are turned into T:
  //    T ~~> T, U ~~> T, V ~~> T, etc.
  // 3. Arrow types, "T -> T" ~~> "T -> T", "U -> U" ~~> "T -> T", and "V -> U" ~~> "T -> U"
  // 4. "U -> BigInt" ~~> "T -> BigInt"

  def getTypeParams(typeTree: TypeTree): Seq[TypeParameter] = {
    def isTypeParameter: TypeTree => Boolean = _.isInstanceOf[TypeParameter]
    def asTypeParameter: TypeTree => TypeParameter = _.asInstanceOf[TypeParameter]
    TypeOps.collectPreorder{ tt => List(tt) }(typeTree)
           .filter(isTypeParameter)
           .map(asTypeParameter)
  }

  def normalizeType(
      allParams: Seq[TypeParameter],
      renamingContext: Map[TypeParameter, TypeParameter],
      typeTree: TypeTree): TypeTree = {
    null
  }

  def normalizeTypes(seq: Seq[TypeTree]): Seq[TypeTree] = {
    val allParams = seq.flatMap(getTypeParams).distinct
    seq.map(typeTree => normalizeType(allParams, Map(), typeTree))
  }

}