import leon.annotation._
import leon.lang._

object DaysToYears {
  val base : Int = 1980

  def isLeapYear(y : Int): Boolean = y % 4 == 0

  def daysToYears(days : Int): Int = {
    require(days > 0)
    daysToYears1(base, days)._1
  }

  def daysToYears1(year : Int, days : Int): (Int, Int) = {
    require(year >= base && days > 0)
    if (days > 366 && isLeapYear(year))
      daysToYears1(year + 1, days - 366)
    else if (days > 365 && !isLeapYear(year))
      daysToYears1(year + 1, days - 365)
    else (year, days)
  } ensuring { res =>
    res._2 <= 366 &&
    res._2 >  0   &&
    res._1 >= base &&
    (((year,days), res) passes {
      case (1980, 366 ) => (1980, 366)
      case (1980, 1000) => (1982, 269)
    })
  }

  @ignore
  def main(args : Array[String]) = {
    println(daysToYears1(base, 10593 ))
    println(daysToYears1(base, 366 ))
    println(daysToYears1(base, 1000 ))
  }
}

