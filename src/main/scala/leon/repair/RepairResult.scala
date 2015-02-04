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
                        repairTrusted: Option[Boolean] = None) {

  def toLine = {
    val benchCat  = f.getParentFile().getName()
    val benchName = f.getName()
    val benchFun  = name

    f"$benchCat%20s, $benchName%20s, $benchFun%20s, $psize%3s, $fsize%3s, ${focusSize.getOrElse("")}%3s, ${initTime.getOrElse("")}%5s, ${focusTime.getOrElse("")}%5s, ${repairTime.getOrElse("")}%5s, ${repairTrusted.getOrElse("")}%5s\n"
  }

}

