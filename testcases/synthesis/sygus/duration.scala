import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Times {
  case class Hour(v: BigInt) {
    def isValid = v >= 0// && v < 24
    def toSeconds = v*3600
  }

  case class Minute(v: BigInt) {
    def isValid = v >= 0 && v < 60
    def toSeconds = v*60
  }

  case class Second(v: BigInt) {
    def isValid = v >= 0 && v < 60
    def toSeconds = v
  }

  case class Time(h: Hour, m: Minute, s: Second) {
    def isValid = {
      h.isValid && m.isValid && s.isValid
    }

    def toSeconds = h.toSeconds + m.toSeconds + s.toSeconds
  }

  def incTime(t: Time, k: BigInt) = {
    choose((tres: Time, seconds: BigInt) => seconds == t.toSeconds && seconds + k == tres.toSeconds && tres.isValid)
  }

  def incTimeInlined(h: BigInt, m: BigInt, s: BigInt, inc: BigInt) = {
    require(
      h >= 0 &&
      m >= 0 && m < 60 &&
      s >= 0 && s < 60 &&
      inc > 0
    )

    choose { (hres: BigInt, mres: BigInt, sres: BigInt) =>
      hres >= 0 &&
      mres >= 0 && mres < 60 &&
      sres >= 0 && sres < 60 &&
      ((hres*3600+mres*60+sres) == ((h*3600 + m*60 + s) + inc))
    }
  }

  def incTime2(m: BigInt, s: BigInt, inc: BigInt) = {
    require(
      m >= 0 &&
      s >= 0 && s < 60 &&
      inc > 0
    )

    ???[(BigInt, BigInt)]

  } ensuring { (res: (BigInt, BigInt)) =>
    val (mres, sres) = res

    mres >= 0 &&
    sres >= 0 && sres < 60 &&
    ((mres*60+sres) == ((m*60 + s) + inc))
  }
}
