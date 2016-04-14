package leon.comparison

import leon.purescala.Definitions.{FunDef, Program}
import leon.utils
import leon.utils.ASCIIHelpers._

/**
  * Created by joachimmuth on 23.03.16.
  *
  */
case class ComparisonReport(base: ComparisonBase, program : Program, listFD: List[(FunDef, FunDef)]) {

  def summaryString : String = {
    import utils.ASCIIHelpers._

    var t = Table("Comparison Summary")

    t ++= listFD.map(
      fd => Row(
        Seq(
          Cell(fd._1.qualifiedName(base.program)),
          Cell(fd._2.qualifiedName(program))
        )
      )
    )


    t += Separator

    t.render



  }

}
