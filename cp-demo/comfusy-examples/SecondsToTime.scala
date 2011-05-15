import cp.Definitions._

object SecondsToTime {
  def main(args: Array[String]): Unit = {
    println("Please enter a number of seconds: ")
    val secnum: Int = Console.readInt

    val (hours, minutes, seconds) = ((h: Int, m: Int, s: Int) => (
           h * 3600 + m * 60 + s == secnum
        && 0 <= m && m < 60
        && 0 <= s && s < 60
      )).solve

    println(secnum + "s = " + hours + "h, " + minutes + "m and " + seconds + "s.")
  }
}

