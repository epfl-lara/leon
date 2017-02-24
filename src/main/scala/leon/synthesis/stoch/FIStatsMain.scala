package leon.synthesis.stoch

import leon.purescala.Definitions.{ClassDef, TypedFunDef}
import leon.purescala.Expressions.{FunctionInvocation, MethodInvocation}
import leon.purescala.Types.TypeTree
import leon.synthesis.stoch.PCFGStats.{addStats, ExprConstrStats}
import leon.synthesis.stoch.PCFGStatsExtractorMain.procFile

object FIStatsMain {

  type FunctionCallStats = Map[TypeTree, Map[TypedFunDef, Seq[FunctionInvocation]]]

  def convertExprConstrToFunctionCallStats(stats: ExprConstrStats): FunctionCallStats = {
    stats.mapValues(ttStats => {
      val ttExprs = ttStats.values.flatten
      ttExprs.filter(_.isInstanceOf[FunctionInvocation])
        .map(_.asInstanceOf[FunctionInvocation])
        .toSeq
        .groupBy(_.tfd)
    })
  }

  def getFunctionCallStatsPretty(stats: FunctionCallStats): String = {
    val ans = new StringBuilder()
    for ((tt, ttStats) <- stats.toList.sortBy { case (_, ttStats) => -ttStats.values.map(_.size).sum }) {
      val ttCount = ttStats.values.map(_.size).sum
      for ((tfd, tfdStats) <- ttStats.toList.sortBy { case (_, tfdStats) => -tfdStats.size }) {
        /* if (tt != tfd.returnType) {
          println(s"Expected type tt = $tt. Found type tfd.returnType = ${tfd.returnType}")
          assert(false)
        } */
        val argTypes = tfd.params.map(_.getType)
        val signature = s"${argTypes.map(_.toString)} => $tt"
        ans.append(s"$tt, $ttCount, ${tfd.signature}, $signature, ${tfdStats.size}\n")
      }
    }
    ans.toString()
  }

  type MethodCallStats = Map[TypeTree, Map[(ClassDef, TypedFunDef), Seq[MethodInvocation]]]

  def convertExprConstrToMethodCallStats(stats: ExprConstrStats): MethodCallStats = {
    stats.mapValues(ttStats => {
      val ttExprs = ttStats.values.flatten
      ttExprs.filter(_.isInstanceOf[MethodInvocation])
        .map(_.asInstanceOf[MethodInvocation])
        .toSeq
        .groupBy(mi => (mi.cd, mi.tfd))
    })
  }

  def getMethodCallStatsPretty(stats: MethodCallStats): String = {
    val ans = new StringBuilder()
    for ((tt, ttStats) <- stats.toList.sortBy { case (_, ttStats) => -ttStats.values.map(_.size).sum }) {
      val ttCount = ttStats.values.map(_.size).sum
      for ((ctfd, ctfdStats) <- ttStats.toList.sortBy { case (_, tfdStats) => -tfdStats.size }) {
        val (cd, tfd) = ctfd
        ans.append(s"$tt $ttCount ${cd.id} ${tfd.signature} ${ctfdStats.size}\n")
      }
    }
    ans.toString()
  }

  def main(args: Array[String]): Unit = {
    @volatile var globalStatsTrain: ExprConstrStats = Map()

    val fileStats = args.tail.par.map(fileName => fileName -> procFile(fileName)).toMap
    for (fileName <- args.tail) {
      globalStatsTrain = addStats(globalStatsTrain, fileStats(fileName))
    }

    println("Printing function invocation stats:")
    val fiStats = convertExprConstrToFunctionCallStats(globalStatsTrain)
    println(getFunctionCallStatsPretty(fiStats))

    println("Printing method invocation stats:")
    val miStats = convertExprConstrToMethodCallStats(globalStatsTrain)
    println(getMethodCallStatsPretty(miStats))
  }

}
