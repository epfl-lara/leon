package leon
package synthesis.stoch

import Statistics._

object StatisticsExtractorMain {

  def main(args: Array[String]): Unit = {
    var globalStats: ExprConstrStats = Map()
    args.par.foreach(fileName => {
      val fileStats = procFile(fileName)
      this.synchronized {
        globalStats = addStats(globalStats, fileStats)
      }
    })
    println(exprConstrStatsToString(globalStats))
  }

  def procFile(fileName: String): ExprConstrStats = {
    val args = List("--pcfg-stats", fileName)
    val ctx = Main.processOptions(args)
    pipeline.run(ctx, args)._2
  }

  def pipeline: Pipeline[List[String], ExprConstrStats] = {
    import frontends.scalac.ClassgenPhase
    import frontends.scalac.ExtractionPhase
    ClassgenPhase andThen ExtractionPhase andThen SimpleFunctionApplicatorPhase(getExprConstrStats)
  }

}