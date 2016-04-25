package leon.comparison

import leon.purescala.Definitions.{FunDef, Program}
import leon.utils
import leon.utils.ASCIIHelpers._

/**
  * Created by joachimmuth on 23.03.16.
  *
  */
case class ComparisonReport(base: ComparisonBase, program : Program, listFD: List[(FunDef, FunDef, Double)]) {

  def summaryString : String = {
    import utils.ASCIIHelpers._

    var t = Table("Comparison Summary")

    t += Row(
      Seq(
        Cell("argument program"),
        Cell("base"),
        Cell("similarity")
      )
    )

    t += Separator

    t ++= listFD.map(
      fd => Row(
        Seq(
          Cell(fd._1.qualifiedName(program)),
          Cell(fd._2.qualifiedName(base.program)),
          Cell(testX(fd._3 * 100) ++ "%")
        )
      )
    )



    t.render
  }

  def testX(d: Double) = new java.text.DecimalFormat("#.##").format(d)

}
