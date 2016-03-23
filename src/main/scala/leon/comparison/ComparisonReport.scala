package leon.comparison

import leon.utils
import leon.utils.ASCIIHelpers.{Cell, Right, Row, Table}

/**
  * Created by joachimmuth on 23.03.16.
  */
case class ComparisonReport() {

  def summaryString : String = {
    import utils.ASCIIHelpers._

    var t = Table("Comparison Summary")

    t += Row(Seq(Cell("coucou")))


    t += Separator

    t.render



  }

}
