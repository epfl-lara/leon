package leon.comparison

import leon.purescala.Definitions.{FunDef, Program}
import leon.{LeonContext, utils}
import leon.utils.ASCIIHelpers._

/**
  * Created by joachimmuth on 23.03.16.
  *
  */
case class ComparisonReport(ctx: LeonContext, base: ComparisonBase, program : Program, comparatorsName: List[String],
listFD: List[(FunDef, FunDef, List[(Double, String)])]) {

  def summaryString : String = {
    import utils.ASCIIHelpers._

    // some information about the rendered table
    ctx.reporter.info("ExprList: compare each expression subtree one by one and count number of exact match" +
      "compared with total number of expression in both function")
    ctx.reporter.info("ClassList: compare each type of expressions one by one and count number of exact" +
      "match compared with total number of expression in both functions")
    ctx.reporter.info("ClassTree: Find the biggest common tree based on type of expression, and count its size" +
      "compared with size of both functions")
    ctx.reporter.info("ScoreTree: Compute a score for the found ClassTree")
    ctx.reporter.info("DirectScoreTree: Find the biggest common tree based directly on a score method, and give the" +
      "score next to the size of both function and the size of the tree.")


    var t = Table("Comparison Summary")

    t += Row(
      Seq(
        Cell("argument program"),
        Cell("base")
        ) ++
        comparatorsName.map(p => Cell(p))
    )

    t += Separator

    t ++= listFD.map(
      fd => Row(
        Seq(
          Cell(fd._1.qualifiedName(program)),
          Cell(fd._2.qualifiedName(base.program))
        ) ++
        fd._3.map(p => Cell(percentage(p._1) + " " + p._2))
      )
    )



    t.render
  }

  private def percentage(d: Double): String = new java.text.DecimalFormat("#.##").format(d*100) ++ "%"

}
