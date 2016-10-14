package leon
package synthesis.stoch

import scala.collection.mutable.HashMap

import leon.LeonContext
import purescala.Definitions.Program
import purescala.ExprOps
import purescala.Expressions.Expr
import purescala.TypeOps
import purescala.Types.TypeParameter
import purescala.Types.TypeTree

object Statistics {

  // All sub-expressions
  def allSubExprs(expr: Expr): Seq[Expr] = ExprOps.collectPreorder{ e => List(e) }(expr)

  def allSubExprs(ctx: LeonContext, p: Program): Seq[Expr] = {
    for {
      unit <- p.units
      f <- unit.definedFunctions
      e <- allSubExprs(f.fullBody)
    } yield e
  }

  def allSubExprsByType(ctx: LeonContext, p: Program): Map[TypeTree, Seq[Expr]] = {
    val ase = allSubExprs(ctx, p)
    val allTypeParams = ase.map(_.getType).flatMap(getTypeParams).distinct
    val ans = ase.groupBy(expr => normalizeType(allTypeParams, expr.getType))
    /* for (typeTree <- ans.keys) {
      println(s"${typeTree}: ${getTypeParams(typeTree)}")
    } */
    ans
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
           .distinct
  }

  def normalizeType(allParams: Seq[TypeParameter], typeTree: TypeTree): TypeTree = {
    val thisParams = getTypeParams(typeTree).distinct
    require(thisParams.toSet.subsetOf(allParams.toSet))
    val renaming = thisParams.zip(allParams)
                             .map { case (x, y) => (x.asInstanceOf[TypeTree], y.asInstanceOf[TypeTree]) }
                             .toMap
    val ans = TypeOps.replace(renaming, typeTree)
    // println(s"Normalizing ${typeTree}: ${ans}")
    ans
  }

  def normalizeTypes(seq: Seq[TypeTree]): Seq[TypeTree] = {
    val allParams = seq.flatMap(getTypeParams).distinct
    seq.map(typeTree => normalizeType(allParams, typeTree))
  }

  // Expression constructor statistics
  type ExprConstrStats = Map[TypeTree, Map[Class[_ <: Expr], Int]]

  def addStats(stats1: ExprConstrStats, stats2: ExprConstrStats): ExprConstrStats = {
    type HashMap[K, V] = scala.collection.mutable.HashMap[K, V]
    val ans = new HashMap[TypeTree, HashMap[Class[_ <: Expr], Int]]()

    def addMap(stats: ExprConstrStats) = {
      for (typeTree <- stats.keys) {
        val typeStats = ans.getOrElse(typeTree, new HashMap())
        for (constr <- stats(typeTree).keys) {
          val freq = typeStats.getOrElse(constr, 0) + stats(typeTree)(constr)
          typeStats.put(constr, freq)
        }
        ans.put(typeTree, typeStats)
      }
    }

    addMap(stats1)
    addMap(stats2)
    ans.mapValues(_.toMap).toMap
  }

  def exprConstrStatsToString(stats: ExprConstrStats): String = {
    val ans = new StringBuilder()
    def total[K](map: Map[K, Int]): Int = map.values.fold(0)(_ + _)
    for (typeConstrs <- stats.toList.sortBy(typeExpr => -total(typeExpr._2))) {
      val typeTotal = total(typeConstrs._2)
      for (constr <- typeConstrs._2.toList.sortBy(-_._2)) {
        ans.append(s"${typeConstrs._1}\t${typeTotal}\t${constr._1}\t${constr._2}\n")
      }
    }
    ans.toString()
  }

  def getExprConstrStats(ctx: LeonContext, p: Program): ExprConstrStats = {
    val asebt: Map[TypeTree, Seq[Expr]] = allSubExprsByType(ctx, p)
    val relevantSubExprs = asebt.mapValues(_.filter(expr => ctx.files.contains(expr.getPos.file)))
                                .filter { case (tt, se) => se.nonEmpty }
    val getExprConstr: Expr => Class[_ <: Expr] = _.getClass
    val asecbt: Map[TypeTree, Seq[Class[_ <: Expr]]] = relevantSubExprs.mapValues(_.map(getExprConstr))
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
