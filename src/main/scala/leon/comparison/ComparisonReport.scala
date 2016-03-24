package leon.comparison

import leon.purescala.Definitions.{FunDef, Program}
import leon.utils
import leon.utils.ASCIIHelpers.{Cell, Right, Row, Table}

/**
  * Created by joachimmuth on 23.03.16.
  */
case class ComparisonReport(program : Program, listFD: List[FunDef]) {

  def summaryString : String = {
    import utils.ASCIIHelpers._

    var t = Table("Comparison Summary")

    t ++= listFD.map(
      fd => Row(
        Seq(
          Cell(fd.qualifiedName(program))
        )
      )
    )


    t += Separator

    t.render



  }

}
