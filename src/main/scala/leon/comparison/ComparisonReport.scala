package leon.comparison

import leon.purescala.Definitions.{FunDef, Program}
import leon.utils
import leon.utils.ASCIIHelpers._

/**
  * Created by joachimmuth on 23.03.16.
  *
  */
case class ComparisonReport(base: ComparisonBase, program : Program, comparatorsName: List[String],
listFD: List[(FunDef, FunDef, List[Double])]) {

  def summaryString : String = {
    import utils.ASCIIHelpers._

    var t = Table("Comparison Summary")

    t += Row(
      Seq(
        Cell("argument program"),
        Cell("base")
      ) ++
      comparatorsName map (Cell(_))
    )

    t += Separator

    t ++= listFD.map(
      fd => Row(
        Seq(
          Cell(fd._1.qualifiedName(program)),
          Cell(fd._2.qualifiedName(base.program))
        ) ++
        fd._3.map(p => Cell(percentage(p)))
      )
    )



    t.render
  }

  def percentage(d: Double) = new java.text.DecimalFormat("#.##").format(d*100) ++ "%"

}
