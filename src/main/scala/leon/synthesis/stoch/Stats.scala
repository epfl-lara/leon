package leon
package synthesis
package stoch

import leon.purescala.Definitions.TypedFunDef
import leon.purescala.Expressions.{Expr, FunctionInvocation, Literal}
import leon.purescala.Types.TypeTree

object Stats {

  type ExprConstrStats = Map[TypeTree, Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]]
  type FunctionCallStats = Map[TypeTree, Map[TypedFunDef, Seq[FunctionInvocation]]]
  type TypeStats = Map[TypeTree, Seq[Expr]]
  type LitStats = Map[TypeTree, Map[Any, Seq[Literal[_]]]]

  def ecsToStringCoarse(stats: ExprConstrStats): String = {
    val ans = new StringBuilder()

    def total1[K1, T](map: Map[K1, Seq[T]]) = map.values.flatten.size
    def total2[K1, K2, T](map: Map[K1, Map[K2, Seq[T]]]): Int = map.values.map(total1).sum

    for ((tt, ttStats) <- stats.toList.sortBy { case (tt, ttStats) => (-total2(ttStats), tt.toString) }) {
      val typeTotal = total2(ttStats)
      val ttStatsSorted = ttStats.toList.sortBy { case (constr, ttConstrStats) => (-total1(ttConstrStats), constr.toString)}
      for ((constr, ttConstrStats) <- ttStatsSorted) {
        val ttConstrStatsSize = ttConstrStats.values.flatten.size
        ans.append(s"$tt, $typeTotal, $constr, $ttConstrStatsSize\n")
      }
    }

    ans.toString()
  }

  def ecsToString(stats: ExprConstrStats): String = {
    val ans = new StringBuilder()

    def total1[K1, T](map: Map[K1, Seq[T]]) = map.values.flatten.size
    def total2[K1, K2, T](map: Map[K1, Map[K2, Seq[T]]]): Int = map.values.map(total1).sum

    for ((tt, ttStats) <- stats.toList.sortBy { case (tt, ttStats) => (-total2(ttStats), tt.toString) }) {
      val typeTotal = total2(ttStats)
      val ttStatsSorted = ttStats.toList.sortBy { case (constr, ttConstrStats) => (-total1(ttConstrStats), constr.toString)}
      for ((constr, ttConstrStats) <- ttStatsSorted) {
        for ((argTypes, es) <- ttConstrStats.toSeq.sortBy { case (argTypes, es) => (-es.size, argTypes.toString())}) {
          val argTypesStr = argTypes.mkString("(", ", ", ")")
          ans.append(s"$tt, $typeTotal, $constr, $argTypesStr, ${es.size}\n")
        }
      }
    }

    ans.toString()
  }

  def fcsToString(stats: FunctionCallStats): String = {
    val ans = new StringBuilder()
    for ((tt, ttStats) <- stats.toList.sortBy { case (_, ttStats) => -ttStats.values.map(_.size).sum }) {
      val ttCount = ttStats.values.map(_.size).sum
      for ((tfd, tfdStats) <- ttStats.toList.sortBy { case (_, tfdStats) => -tfdStats.size }) {
        val argTypes = tfd.params.map(_.getType)
        val argTypeSign = if (argTypes.size != 1) argTypes.mkString("(", ", ", ")") else argTypes.head.toString
        val signature = s"$argTypeSign => ${tfd.returnType}"
        ans.append(s"$tt, $ttCount, ${tfd.signature}: $signature, ${tfdStats.size}\n")
      }
    }
    ans.toString()
  }

  def tsToString(stats: TypeStats): String = {
    val ans = new StringBuilder()
    for ((tt, ttStats) <- stats.toList.sortBy { case (_, ttStats) => -ttStats.size }) {
      ans.append(s"$tt, ${ttStats.size}\n")
    }
    ans.toString()
  }

  def lsToString(stats: LitStats): String = {
    val ans = new StringBuilder()
    for ((tt, ttStats) <- stats.toList.sortBy { case (_, ttStats) => -ttStats.values.map(_.size).sum }) {
      val ttCount = ttStats.values.map(_.size).sum
      for ((value, tvStats) <- ttStats.toList.sortBy { case (_, tvStats) => -tvStats.size }) {
        ans.append(s"$tt, $ttCount, $value, ${tvStats.size}\n")
      }
    }
    ans.toString()
  }

}