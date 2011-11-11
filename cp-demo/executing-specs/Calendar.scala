import cp.Definitions._
import cp.Terms._

object Calendar extends App {
  // Declaratively computes a year and extra number of days since January first 1980.
  // A piece of (imperative) code performing the same computation was responsible
  // for a bug in a popular Mp3 player.

  final val totalDays = 10593
  final val originYear = 1980

  @spec def leapDaysUntil(y: Int) = (y - 1) / 4 - (y - 1) / 100 + (y - 1) / 400

  val (year, day) = ((year: Int, day: Int) => 
    totalDays == (year - originYear) * 365 + leapDaysUntil(year) - leapDaysUntil(originYear) + day &&
    day > 0 && day <= 366).solve

  println("Year : %d, day : %d" format (year, day))
}
