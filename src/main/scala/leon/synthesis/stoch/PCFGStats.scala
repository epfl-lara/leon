package leon
package synthesis
package stoch

import purescala.Definitions.{Program, TypedFunDef}
import purescala.Expressions.{Expr, FunctionInvocation}
import purescala.{ExprOps, TypeOps}
import purescala.Types.{TypeParameter, TypeTree}

object PCFGStats {

  // All sub-expressions
  def allSubExprs(expr: Expr): Seq[Expr] = ExprOps.collectPreorder{ e => List(e) }(expr)

  def allSubExprs(p: Program): Seq[Expr] = {
    for {
      unit <- p.units if unit.isMainUnit
      f <- unit.definedFunctions
      e <- allSubExprs(f.fullBody)
    } yield e
  }

  def allSubExprsByType(p: Program): Map[TypeTree, Seq[Expr]] = {
    val ase = allSubExprs(p)
    val allTypeParams = ase.map(_.getType).flatMap(getTypeParams).distinct
    ase.groupBy(expr => normalizeType(allTypeParams, expr.getType))
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
  type ExprConstrStats = Map[TypeTree, Map[Class[_ <: Expr], Seq[Expr]]]

  def addStats(stats1: ExprConstrStats, stats2: ExprConstrStats): ExprConstrStats = {
    type HashMap[K, V] = scala.collection.mutable.HashMap[K, V]
    val ans = new HashMap[TypeTree, HashMap[Class[_ <: Expr], Seq[Expr]]]()

    def addMap(stats: ExprConstrStats) = {
      for (typeTree <- stats.keys) {
        val typeStats = ans.getOrElse(typeTree, new HashMap())
        for (constr <- stats(typeTree).keys) {
          val freq = typeStats.getOrElse(constr, Seq()) ++ stats(typeTree)(constr)
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

    def total[K, T](map: Map[K, Seq[T]]): Int = map.mapValues(_.size).values.sum
    for ((tt, ttStats) <- stats.toList.sortBy{ case (tt, ttStats) => (-total(ttStats), tt.toString) }) {
      val typeTotal = total(ttStats)
      val ttStatsSorted = ttStats.mapValues(_.size).toSeq.sortBy { case (constr, freq) => (-freq, constr.toString) }
      for ((constr, freq) <- ttStatsSorted) {
        ans.append(s"$tt\t$typeTotal\t$constr\t$freq\n")
      }
    }
    ans.toString()
  }

  def getExprConstrStats(ctx: LeonContext, p: Program): ExprConstrStats = {
    allSubExprsByType(p).mapValues(_.groupBy(_.getClass))
  }

  // Type statistics
  def getTypeStats(ctx: LeonContext, p: Program): Map[TypeTree, Int] = {
    allSubExprs(p).groupBy(_.getType).mapValues(_.size)
  }

  def getTypeStatsPretty(ctx: LeonContext, p: Program): String = {
    val ans = new StringBuilder()
    for (typeFreq <- getTypeStats(ctx, p).toList.sortBy(-_._2)) {
      ans.append(s"${typeFreq._1} -> ${typeFreq._2}\n")
    }
    ans.toString()
  }

  // Expression constructor statistics
  type FunctionInvocationStats = Map[TypeTree, Map[TypedFunDef, Seq[FunctionInvocation]]]

  def convertExprConstrToFunctionInvocationStats(stats: ExprConstrStats): FunctionInvocationStats = {
    stats.mapValues(ttStats => {
      val ttExprs = ttStats.values.flatten
      ttExprs.filter(_.isInstanceOf[FunctionInvocation])
             .map(_.asInstanceOf[FunctionInvocation])
             .toSeq
             .groupBy(_.tfd)
    })
  }

  def getFunctionInvocationStatsPretty(stats: FunctionInvocationStats): String = {
    val ans = new StringBuilder()
    for ((tt, ttStats) <- stats) {
      val ttCount = ttStats.values.map(_.size).sum
      for ((tfd, tfdStats) <- ttStats) {
        ans.append(s"$tt $ttCount $tfd ${tfdStats.size}\n")
      }
    }
    ans.toString()
  }

}
