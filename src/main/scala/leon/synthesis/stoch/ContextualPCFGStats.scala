package leon
package synthesis
package stoch

import purescala.Definitions.Program
import purescala.ExprOps
import purescala.Expressions.Expr
import purescala.Types.TypeTree
import StatsUtils._

object ContextualPCFGStats {

  type ConstrAnc = Seq[(Class[_ <: Expr], Int)]
  type AncStats = Map[TypeTree, Map[ConstrAnc, Map[Class[_ <: Expr], Int]]]

  def allSubExprsWithAncestry(expr: Expr): Seq[Seq[(Expr, Int)]] = {
    def op(e: Expr, subs: Seq[Seq[Seq[(Expr, Int)]]]): Seq[Seq[(Expr, Int)]] = {
      val subsPrime = for {
        i <- subs.indices
        sp <- subs(i)
      } yield sp :+ (e, i)
      Seq((e, 0)) +: subsPrime
    }
    ExprOps.fold(op)(expr)
  }

  def allSubExprsWithAncestry(p: Program): Seq[Seq[(Expr, Int)]] = for {
    unit <- p.units if unit.isMainUnit
    f <- unit.definedFunctions
    e <- allSubExprsWithAncestry(f.fullBody)
  } yield e

  def getAncStats(ctx: LeonContext, p: Program): AncStats = {
    val ase = allSubExprsWithAncestry(p)

    def exprType(es: Seq[(Expr, Int)]): TypeTree = normalizeType(es.head._1.getType)
    def exprConstr(es: Seq[(Expr, Int)]): Class[_ <: Expr] = es.head._1.getClass
    def constrAnc(es: Seq[(Expr, Int)]): ConstrAnc = es.tail.map{ case (e, idx) => (e.getClass, idx) }

    for ((tt, ttAse) <- ase.groupBy(exprType))
    yield {
      val tg1 = for ((anc, ttAncAse) <- ttAse.groupBy(constrAnc))
                yield {
                  val tg2 = ttAncAse.groupBy(exprConstr).mapValues(_.size)
                  anc -> tg2
                }
      tt -> tg1
    }
  }

  def addStats(stats1: AncStats, stats2: AncStats): AncStats = {
    type HashMap[K, V] = scala.collection.mutable.HashMap[K, V]
    val ans = new HashMap[TypeTree, HashMap[ConstrAnc, HashMap[Class[_ <: Expr], Int]]]()

    def addMap(stats: AncStats) = {
      for (tt <- stats.keys) {
        val ttStats = ans.getOrElseUpdate(tt, new HashMap())
        for (anc <- stats(tt).keys) {
          val ttAncStats = ttStats.getOrElseUpdate(anc, new HashMap())
          for (constr <- stats(tt)(anc).keys) {
            val freq = ttAncStats.getOrElse(constr, 0) + stats(tt)(anc)(constr)
            ttAncStats.put(constr, freq)
          }
        }
      }
    }

    addMap(stats1)
    addMap(stats2)
    ans.mapValues(_.mapValues(_.toMap).toMap).toMap
  }

  def reduceContextDepth(anc: ConstrAnc, newDepth: Int): ConstrAnc = anc.take(newDepth - 1)

  def reduceContextDepth(stats: AncStats, newDepth: Int): AncStats = {
    for ((tt, ttStats) <- stats)
    yield {
      type HashMap[K, V] = scala.collection.mutable.HashMap[K, V]
      val temp = new HashMap[ConstrAnc, HashMap[Class[_ <: Expr], Int]]()

      for (anc <- ttStats.keys) {
        val ttAncStats = temp.getOrElseUpdate(reduceContextDepth(anc, newDepth), new HashMap())
        for (constr <- stats(tt)(anc).keys) {
          val freq = ttAncStats.getOrElse(constr, 0) + stats(tt)(anc)(constr)
          ttAncStats.put(constr, freq)
        }
      }

      tt -> temp.mapValues(_.toMap).toMap
    }
  }

  def ancStatsToString(stats: AncStats): String = {
    val ans = new StringBuilder()
    val sortedTTs = stats.keys.toList.sortBy(tt => (-stats(tt).values.flatMap(_.values).sum, tt.toString))
    for (tt <- sortedTTs) {
      val statsTTSum = stats(tt).values.flatMap(_.values).sum
      val sortedAncs = stats(tt).keys.toList.sortBy(anc => (-stats(tt)(anc).values.sum, anc.toString()))
      for (anc <- sortedAncs) {
        val statsTTAncSum = stats(tt)(anc).values.sum
        val sortedConstrs = stats(tt)(anc).keys.toList.sortBy(constr => (-stats(tt)(anc)(constr), constr.toString))
        for (constr <- sortedConstrs) {
          ans.append(s"$tt, $statsTTSum, $anc, $statsTTAncSum, $constr, ${stats(tt)(anc)(constr)}\n")
        }
      }
    }
    ans.toString()
  }

}
