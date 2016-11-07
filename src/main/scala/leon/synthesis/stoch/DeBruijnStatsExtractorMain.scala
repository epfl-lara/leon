package leon
package synthesis
package stoch

import DeBruijnStats.getDeBruijnStats

import scala.collection.mutable

object DeBruijnStatsExtractorMain {

  def main(args: Array[String]): Unit = {
    val ans = new mutable.MutableList[(Int, Int, Double)]()

    args.tail.par.foreach(fileName => {
      val res = procFile(fileName)
      ans.synchronized {
        for (dbs <- res if dbs.scope.size > 0) {
          ans += ((dbs.dist, dbs.scope.size, dbs.relDist))
        }
      }
      println(s"Finished processing ${fileName}")
    })

    for (df <- ans.groupBy(_._1)) {
      println(s"${df._1}, ${df._2.size}")
    }
    println("---")

    for (df <- ans.groupBy(_._3)) {
      println(s"${df._1}, ${df._2.size}")
    }
    println("---")
  }

  def procFile(fileName: String): Seq[DeBruijnStats] = {
    val args = List(fileName)
    val ctx = Main.processOptions(args)
    pipeline.run(ctx, args)._2
  }

  def pipeline: Pipeline[List[String], Seq[DeBruijnStats]] = {
    import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
    ClassgenPhase andThen ExtractionPhase andThen SimpleFunctionApplicatorPhase(getDeBruijnStats)
  }

}
