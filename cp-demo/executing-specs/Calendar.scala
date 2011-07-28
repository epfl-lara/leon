import cp.Definitions._
import cp.Terms._

object Calendar extends App {
  
  final val totalDays = 10593
  final val originYear = 1980

  val (year, day) = ((year : Int, day : Int) => totalDays == (year - originYear) * 365 + (year - 1) / 4 - (year - 1) / 100 + (year - 1) / 400 -
    ((originYear - 1) / 4 - (originYear - 1) / 100 + (originYear - 1) / 400) + day &&
    day > 0 && day <= 366).solve

  println("Year : %d, day : %d" format (year, day))

  /* alternate version with intermediate "leapDaysUntil" variables

  def yearAndDay(totalDays : Int, originYear : Int) : (Int, Int) = {
    val (y, d, _, _) = ((year : Int, day : Int, lduYear : Int, lduOrigin : Int) => totalDays == (year - originYear) * 365 + lduYear - lduOrigin + day &&
      lduYear == (year - 1) / 4 - (year - 1) / 100 + (year - 1) / 400 &&
      lduOrigin == ((originYear - 1) / 4 - (originYear - 1) / 100 + (originYear - 1) / 400) &&
      day > 0 && day <= 366).solve
    
    (y, d)
  }
  */
    
}

