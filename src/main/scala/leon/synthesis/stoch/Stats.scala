package leon
package synthesis
package stoch

import leon.purescala.Expressions.{Expr, FunctionInvocation, Literal}
import leon.purescala.Types.TypeTree
import leon.utils.Position

import scala.collection.mutable

object Stats {

  // Normalized expression type -> Constructor -> ArgType* -> Expr*
  type ExprConstrStats = Map[TypeTree, Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]]
  // Normalized expression type -> Position of function definition -> Expression*
  type FunctionCallStats = Map[TypeTree, Map[Position, Seq[FunctionInvocation]]]
  // Normalized expression type -> Expr*
  type TypeStats = Map[TypeTree, Seq[Expr]]
  // Normalized expression type -> Value -> (Literal[_] <: Expr)*
  type LitStats = Map[TypeTree, Map[Any, Seq[Literal[_]]]]

  // Normalized expression type -> Relation to parent -> Constructor -> ArgType* -> Expr*
  type ECS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]]]
  // Normalized expression type -> Relation to parent -> Position of function definition -> Expression*
  type FCS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Position, Seq[FunctionInvocation]]]]
  // Normalized expression type -> Relation to parent -> Value -> (Literal[_] <: Expr)*
  type LS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Any, Seq[Literal[_]]]]]

  def ecsAdd(ecs1: ExprConstrStats, ecs2: ExprConstrStats): ExprConstrStats = {
    val ans = new mutable.HashMap[TypeTree, Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]]()
    for (tt <- ecs1.keySet ++ ecs2.keySet) {
      val ansTT = new mutable.HashMap[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]()
      val ecs1TT = ecs1.getOrElse(tt, Map())
      val ecs2TT = ecs2.getOrElse(tt, Map())
      for (constr <- ecs1TT.keySet ++ ecs2TT.keySet) {
        val ansTTConstr = new mutable.HashMap[Seq[TypeTree], Seq[Expr]]()
        val ecs1TTConstr = ecs1TT.getOrElse(constr, Map())
        val ecs2TTConstr = ecs2TT.getOrElse(constr, Map())
        for (stt <- ecs1TTConstr.keySet ++ ecs2TTConstr.keySet) {
          val ecs1TTConstrSTT = ecs1TTConstr.getOrElse(stt, Seq())
          val ecs2TTConstrSTT = ecs2TTConstr.getOrElse(stt, Seq())
          ansTTConstr += stt -> (ecs1TTConstrSTT ++ ecs2TTConstrSTT)
        }
        ansTT += constr -> ansTTConstr.toMap
      }
      ans += tt -> ansTT.toMap
    }
    ans.toMap
  }

  def ecs2Add(ecs1: ECS2, ecs2: ECS2): ECS2 = {
    val ans = new mutable.HashMap[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]]]()
    for (tt <- ecs1.keySet ++ ecs2.keySet) {
      val ansTT = new mutable.HashMap[Option[(Int, Class[_ <: Expr])], Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]]()
      val ecs1TT = ecs1.getOrElse(tt, Map())
      val ecs2TT = ecs2.getOrElse(tt, Map())
      for (parent <- ecs1TT.keySet ++ ecs2TT.keySet) {
        val ansTTPar = new mutable.HashMap[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]()
        val ecs1TTPar = ecs1TT.getOrElse(parent, Map())
        val ecs2TTPar = ecs2TT.getOrElse(parent, Map())
        for (constr <- ecs1TTPar.keySet ++ ecs2TTPar.keySet) {
          val ansTTParConstr = new mutable.HashMap[Seq[TypeTree], Seq[Expr]]()
          val ecs1TTParConstr = ecs1TTPar.getOrElse(constr, Map())
          val ecs2TTParConstr = ecs2TTPar.getOrElse(constr, Map())
          for (stt <- ecs1TTParConstr.keySet ++ ecs2TTParConstr.keySet) {
            val ecs1TTParConstrSTT = ecs1TTParConstr.getOrElse(stt, Seq())
            val ecs2TTParConstrSTT = ecs2TTParConstr.getOrElse(stt, Seq())
            ansTTParConstr += stt -> (ecs1TTParConstrSTT ++ ecs2TTParConstrSTT)
          }
          ansTTPar += constr -> ansTTParConstr.toMap
        }
        ansTT += parent -> ansTTPar.toMap
      }
      ans += tt -> ansTT.toMap
    }
    ans.toMap
  }

  def ecsToStringCoarse(stats: ExprConstrStats): String = {
    val ans = new StringBuilder()

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

  def ecs2ToStringCoarse(stats: ECS2): String = {
    val ans = new StringBuilder()

    for ((tt, ttStats) <- stats.toList.sortBy { case (tt, ttStats) => (-total3(ttStats), tt.toString) }) {
      val ttTotal = total3(ttStats)
      val ttStatsSorted = ttStats.toList.sortBy { case (par, ttParStats) => (-total2(ttParStats), par.toString) }
      for ((par, ttParStats) <- ttStatsSorted) {
        val ttParTotal = total2(ttParStats)
        val ttParStatsSorted = ttParStats.toList.sortBy { case (constr, ttParConstrStats) => (-total1(ttParConstrStats), constr.toString) }
        for ((constr, ttParConstrStats) <- ttParStatsSorted) {
          val ttParConstrStatsSize = ttParConstrStats.values.flatten.size
          ans.append(s"$tt, $ttTotal, $par, $ttParTotal, $constr, $ttParConstrStatsSize\n")
        }
      }
    }

    ans.toString()
  }

  def ecsToString(stats: ExprConstrStats): String = {
    val ans = new StringBuilder()

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

  def ecs2ToString(stats: ECS2): String = {
    val ans = new StringBuilder()

    for ((tt, ttStats) <- stats.toList.sortBy { case (tt, ttStats) => (-total3(ttStats), tt.toString) }) {
      val ttTotal = total3(ttStats)
      val ttStatsSorted = ttStats.toList.sortBy { case (par, ttParStats) => (-total2(ttParStats), par.toString) }
      for ((par, ttParStats) <- ttStatsSorted) {
        val ttParTotal = total2(ttParStats)
        val ttParStatsSorted = ttParStats.toList.sortBy { case (constr, ttParConstrStats) => (-total1(ttParConstrStats), constr.toString) }
        for ((constr, ttParConstrStats) <- ttParStatsSorted) {
          for ((argTypes, es) <- ttParConstrStats.toSeq.sortBy { case (argTypes, es) => (-es.size, argTypes.toString()) }) {
            val argTypesStr = argTypes.mkString("(", ", ", ")")
            ans.append(s"$tt, $ttTotal, $par, $ttParTotal, $constr, $argTypesStr, ${es.size}\n")
          }
        }
      }
    }

    ans.toString()
  }

  def fcsToString(stats: FunctionCallStats): String = {
    val ans = new StringBuilder()
    for ((tt, ttStats) <- stats.toList.sortBy { case (_, ttStats) => -ttStats.values.map(_.size).sum }) {
      val ttCount = total1(ttStats)
      for ((pos, tfdStats) <- ttStats.toList.sortBy { case (_, tfdStats) => -tfdStats.size }) {
        val tfd = tfdStats.head.tfd
        val argTypes = tfd.params.map(_.getType)
        val argTypeSign = if (argTypes.size != 1) argTypes.mkString("(", ", ", ")") else argTypes.head.toString
        val signature = s"$argTypeSign => ${tfd.returnType}"
        ans.append(s"$tt, $ttCount, ${tfd.signature}: $signature, ${tfdStats.size}\n")
      }
    }
    ans.toString()
  }

  def fcs2ToString(stats: FCS2): String = {
    val ans = new StringBuilder()
    for ((tt, ttStats) <- stats.toList.sortBy { case (tt, ttStats) => (-total2(ttStats), tt.toString) }) {
      val ttTotal = total2(ttStats)
      val ttStatsSorted = ttStats.toSeq.sortBy { case (par, ttParStats) => (-total1(ttParStats), par.toString) }
      for ((par, ttParStats) <- ttStatsSorted) {
        val ttParTotal = total1(ttParStats)
        val ttParStatsSorted = ttParStats.toSeq.sortBy { case (pos, fis) => (-fis.size, pos.toString) }
        for ((pos, fis) <- ttParStatsSorted) {
          val tfd = fis.head.tfd
          val argTypes = tfd.params.map(_.getType)
          val argTypeSign = if (argTypes.size != 1) argTypes.mkString("(", ", ", ")") else argTypes.head.toString
          val signature = s"$argTypeSign => ${tfd.returnType}"
          ans.append(s"$tt, $ttTotal, $par, $ttParTotal, ${tfd.signature}: $signature, ${fis.size}\n")
        }
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

  def ls2ToString(stats: LS2): String = {
    val ans = new StringBuilder()
    for ((tt, ttStats) <- stats.toSeq.sortBy { case (tt, ttStats) => (-total2(ttStats), tt.toString) }) {
      val ttCount = total2(ttStats)
      for ((par, ttParStats) <- ttStats.toSeq.sortBy { case (par, ttParStats) => (-total1(ttParStats), par.toString) }) {
        val ttParCount = total1(ttParStats)
        for ((value,  literals) <- ttParStats.toSeq.sortBy { case (_, literals) => -literals.size }) {
          ans.append(s"$tt, $ttCount, $par, $ttParCount, $value, ${literals.size}\n")
        }
      }
    }
    ans.toString()
  }

  def total1[K1, T](map: Map[K1, Seq[T]]): Int = map.values.flatten.size
  def total2[K1, K2, T](map: Map[K1, Map[K2, Seq[T]]]): Int = map.values.map(total1).sum
  def total3[K1, K2, K3, T](map: Map[K1, Map[K2, Map[K3, Seq[T]]]]): Int = map.values.map(total2).sum

}
