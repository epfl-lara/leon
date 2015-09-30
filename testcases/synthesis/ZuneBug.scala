import leon.lang._
import leon.lang.synthesis._

/* Inspired by the Zune bug that caused looping. 
   This encodes the task of date conversion into 
   integer linear arithmetic and tries to synthesize it.
*/

object ZuneBug {
  @inline
  def leapsTill(year: BigInt): BigInt = {
    require(year >= 0)
    val y1 = year - 1
    y1/4 + y1/100 + y1/400
  }

  @inline
  def isLeap(year: BigInt): Boolean = {
    require(year >= 0)
    leapsTill(year+1) > leapsTill(year)
  }

  // wrong, accidentaly underspecified
  def yearDayConfused(daysSince1980: BigInt): (BigInt, BigInt) = {
    require(daysSince1980 >= 0)
    ???[(BigInt,BigInt)]
  } ensuring (res => {
    val (year, day) = res
    year >= 1980 &&
    0 <= day && day <= 366 &&
    (day == 366 ==> isLeap(year)) &&
    daysSince1980 == (year - 1980)*365 +
      leapsTill(year) - leapsTill(1980) + day
  })

  // should be correct
  def yearDay(daysSince1980: BigInt): (BigInt, BigInt) = {
    require(daysSince1980 >= 0)
    ???[(BigInt,BigInt)]
  } ensuring (res => {
    val (year, day) = res
    year >= 1980 &&
    0 <= day && day <= 365 &&
    (day == 365 ==> isLeap(year)) &&
    daysSince1980 == (year - 1980)*365 +
      leapsTill(year) - leapsTill(1980) + day
  })

  // test run-time constraint solving. smt-cvc4 seems fastest
  def testYearDay = {
    (yearDay(364),
     yearDay(365),
     yearDay(366),
     yearDay(366+364),
     yearDay(366+365))
  }

}
