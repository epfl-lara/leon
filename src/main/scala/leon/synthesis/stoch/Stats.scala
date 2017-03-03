package leon
package synthesis
package stoch

import leon.purescala.Definitions.TypedFunDef
import leon.purescala.Expressions.{Expr, FunctionInvocation, Literal}
import leon.purescala.Types.TypeTree

object Stats {

  type ExprConstrStats = Map[TypeTree, Map[Class[_ <: Expr], Seq[Expr]]]
  type FunctionCallStats = Map[TypeTree, Map[TypedFunDef, Seq[FunctionInvocation]]]
  type TypeStats = Map[TypeTree, Seq[Expr]]
  type LitStats = Map[TypeTree, Map[Any, Seq[Literal[_]]]]

  def ecsToString(stats: ExprConstrStats): String = {
    val ans = new StringBuilder()

    def total[K, T](map: Map[K, Seq[T]]): Int = map.mapValues(_.size).values.sum
    for ((tt, ttStats) <- stats.toList.sortBy{ case (tt, ttStats) => (-total(ttStats), tt.toString) }) {
      val typeTotal = total(ttStats)
      val ttStatsSorted = ttStats.mapValues(_.size).toSeq.sortBy { case (constr, freq) => (-freq, constr.toString) }
      for ((constr, freq) <- ttStatsSorted) {
        ans.append(s"$tt, $typeTotal, $constr, $freq\n")
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