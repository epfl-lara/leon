package leon.comparison

import leon.purescala.Definitions.{FunDef, Program}
import leon.{LeonContext}
import leon.utils.ASCIIHelpers._

/**
  * Created by joachimmuth on 23.03.16.
  *
  */
case class ComparisonReport(ctx: LeonContext, base: ComparisonBase, program : Program, comparatorsName: List[String],
listFD: List[(FunDef, FunDef, List[(Double, String)])]) {

  def summaryString : String = {

    // some information about the rendered table
    ctx.reporter.info("argument program: name of compared function and its size")
    ctx.reporter.info("base: name of function extracted from our corpus and its size")
    ctx.reporter.info("ExprList: compare each expression subtree one by one and count number of exact match" +
      "compared with total number of expression in both function")
    ctx.reporter.info("ClassList: compare each type of expressions one by one and count number of exact" +
      "match compared with total number of expression in both functions")
    ctx.reporter.info("ClassTree: Find the biggest common tree based on type of expression, and count its size" +
      "compared with size of both functions")
    ctx.reporter.info("ScoreTree: Compute a score for the found ClassTree")
    ctx.reporter.info("DirectScoreTree: Find the biggest common tree based directly on a score method, and give the" +
      "score next to the size of both function and the size of the tree.")



    // report table
    var t = Table("Comparison Summary")

    t += Row(
      Seq(
        Cell("argument program"),
        Cell("size"),
        Cell("base"),
        Cell("size")
        ) ++
        comparatorsName.map(p => Cell(p))
    )

    t += Separator

    t ++= listFD.map(
      fd => Row(
        Seq(
          Cell(fd._1.qualifiedName(program)),
          Cell(size(fd._1)),
          Cell(fd._2.qualifiedName(base.program)),
          Cell(size(fd._2))
        ) ++
        fd._3.map(p => Cell(percentage(p._1) + " " + p._2))
      )
    )



    t.render
  }

  private def percentage(d: Double): String = new java.text.DecimalFormat("#.##").format(d*100) ++ "%"

  private def size(f: FunDef): String = "(" + Utils.collectExpr(f.body.get).size + ")"

}
