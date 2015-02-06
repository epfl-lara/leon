package leon
package repair

import java.io.File

case class RepairResult(f: File,
                        psize: Int,
                        fsize: Int = -1,
                        name: String = "?",
                        initTime: Option[Long] = None,
                        focusTime: Option[Long] = None,
                        focusSize: Option[Int] = None,
                        repairTime: Option[Long] = None,
                        repairSize: Option[Int] = None,
                        repairTrusted: Option[Boolean] = None) {

  def toLine = {
    val benchCat  = f.getAbsoluteFile().getParentFile().getName()
    val benchName = f.getName()
    val benchFun  = name

    f"$benchCat%20s, $benchName%20s, $benchFun%20s, $psize%3s, $fsize%3s, ${focusSize.getOrElse("")}%3s, ${initTime.getOrElse("")}%5s, ${focusTime.getOrElse("")}%5s, ${repairTime.getOrElse("")}%5s, ${repairTrusted.getOrElse("")}%5s\n"
  }

  def toTableLine = {
    val benchCat  = f.getAbsoluteFile().getParentFile().getName()
    val benchName = f.getName()
    val benchFun  = name

    def ts(ot: Option[Long]): String = {
      val s = ot.map{
        ms => 
          val t: Double = Math.round(ms/100.0)/10.0
          f"$t%.1f"
      }.getOrElse("")

      f"$s%5s"
    }

    val verified = repairTrusted.map(if (_) "\\chmark" else "").getOrElse("")

    val repairTime2 = (focusTime, repairTime) match {
      case (Some(t), Some(t2)) => Some(t + t2)
      case _ => None
    }

    f"$benchCat%20s &  $benchName%20s & $benchFun%20s & $psize%4s & $fsize%3s & ${focusSize.getOrElse("")}%3s & ${repairSize.getOrElse("")}%3s & ${ts(initTime)} & ${ts(repairTime2)} & $verified%7s \\\\ \n"
  }
}

