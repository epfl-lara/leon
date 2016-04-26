package leon.comparison

import leon.purescala.Definitions.{FunDef, Program}
import leon.utils
import leon.utils.ASCIIHelpers._

/**
  * Created by joachimmuth on 23.03.16.
  *
  */
case class ComparisonReport(base: ComparisonBase, program : Program, listFD: List[(FunDef, FunDef, Double, Double)]) {

  def summaryString : String = {
    import utils.ASCIIHelpers._

    var t = Table("Comparison Summary")

    t += Row(
      Seq(
        Cell("argument program"),
        Cell("base"),
        Cell("similarity List"),
        Cell("similarity Tree")
      )
    )

    t += Separator

    t ++= listFD.map(
      fd => Row(
        Seq(
          Cell(fd._1.qualifiedName(program)),
          Cell(fd._2.qualifiedName(base.program)),
          Cell(percentage(fd._3)),
          Cell(percentage(fd._4))
        )
      )
    )



    t.render
  }

  def percentage(d: Double) = new java.text.DecimalFormat("#.##").format(d*100) ++ "%"

}
