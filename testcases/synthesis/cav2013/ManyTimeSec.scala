import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object ManyTimeSec { 
  case class Time(h:Int,m:Int,s:Int)
  case class Seconds(total:Int)

  def timeAndSec(t:Time,seconds:Seconds) : Boolean = {
    3600*t.h + 60*t.m + t.s == seconds.total && 
    t.h >= 0 && t.m >= 0 && t.m < 60 && t.s >= 0 && t.s < 60
  }
  def time2sec(t:Time) : Seconds = 
    choose((seconds:Seconds) => timeAndSec(t,seconds))
  def sec2time(seconds:Seconds):Time = 
    choose((t:Time) => timeAndSec(t,seconds))

  def incTime(t0:Time,k:Int) : Time =
    choose((t1:Time) => time2sec(t1).total == time2sec(t0).total + k)

  def testDetuple1(k:Int) : Seconds = {
    choose((seconds0:Seconds) => 
      k == 2*seconds0.total
    )
  }
  def testDetuple2(total:Int) : Time = {
    require(0 <= total)
    choose((t:Time) => 
      3600*t.h + 60*t.m + t.s == total && 
	   t.h >= 0 && t.m >= 0 && t.m < 60 && t.s >= 0 && t.s < 60
    )
  }

  def incTimeUnfolded(t0:Time,k:Int) : Time = {
    require(0 <= t0.h && 0 <= t0.m && t0.m < 60 && 0 <= t0.s && t0.s < 60)
    choose((t1:Time,seconds0:Seconds) => 
      3600*t0.h + 60*t0.m + t0.s == seconds0.total && 
      3600*t1.h + 60*t1.m + t1.s == seconds0.total + k && 
      t1.h >= 0 && t1.m >= 0 && t1.m < 60 && t1.s >= 0 && t1.s < 60      
    )._1
  }

  def incTimeUnfoldedOutOnly(t0:Time,k:Int) : Time = {
    require(0 <= t0.h && 0 <= t0.m && t0.m < 60 && 0 <= t0.s && t0.s < 60)
    val total = k + 3600*t0.h + 60*t0.m + t0.s
    choose((t1:Time) => 
      3600*t1.h + 60*t1.m + t1.s == total + k && 
      t1.h >= 0 && t1.m >= 0 && t1.m < 60 && t1.s >= 0 && t1.s < 60      
    )
  }

  def incTime2(h1:Int,m1:Int,s1:Int,k:Int) : (Int,Int,Int) = {
    require(0 <= k && 0 <= h1 && 0 <= m1 && m1 < 60 && 0 <= s1 && s1 < 60)
    choose((h2:Int,m2:Int,s2:Int) => 
      0 <= m2 && m2 < 60 && 0 <= s2 && s2 < 60 &&
      3600*h2+60*m2+s2 == 3600*h1+60*m1+s1 + k)
  }

  def incTime2one(h1:Int,m1:Int,s1:Int) : (Int,Int,Int) = {
    require(0 <= h1 && 0 <= m1 && m1 < 60 && 0 <= s1 && s1 < 60)
    choose((h2:Int,m2:Int,s2:Int) => 
      0 <= m2 && m2 < 60 && 0 <= s2 && s2 < 60 &&
      3600*h2+60*m2+s2 == 3600*h1+60*m1+s1 + 1)
  }

  // Yes, we can, do it without multiply and divide
  def incTime3one(h1:Int,m1:Int,s1:Int) : (Int,Int,Int) = {
    require(0 <= h1 && 0 <= m1 && m1 < 60 && 0 <= s1 && s1 < 60)
    if (s1 + 1 < 60)
      (h1,m1,s1+1)
    else
      if (m1 + 1 < 60)
	(h1,m1+1,0)
      else
	(h1+1,0,0)
  } ensuring(res => {
    val (h2,m2,s2) = res
    0 <= m2 && m2 < 60 && 0 <= s2 && s2 < 60 && 
    3600*h2+60*m2+s2 == 3600*h1+60*m1+s1 + 1
  })

  case class RedundantTime(t:Time, s:Seconds)
  def isOkRT(rt:RedundantTime) : Boolean = timeAndSec(rt.t, rt.s)

  def incRT(rt0:RedundantTime, k:Int) : RedundantTime = {
    require(isOkRT(rt0))
    choose((rt1:RedundantTime) => isOkRT(rt1) && rt1.s.total == rt0.s.total + k)
  }

  abstract class RedundantTimeList
  case class Nil() extends RedundantTimeList
  case class Cons(head:RedundantTime,tail:RedundantTimeList) extends RedundantTimeList

  def isInced(l1:RedundantTimeList, k:Int, l2:RedundantTimeList) : Boolean = {
    (l1,l2) match {
      case (Nil(),Nil()) => true
      case (Cons(rt1,rest1),Cons(rt2,rest2)) => {
	isOkRT(rt1) && isOkRT(rt2) &&
	(rt2.s.total == rt2.s.total + k) &&
        isInced(rest1,k,rest2)
      }
      case _ => false
    }
  }

  def incAll(l:RedundantTimeList, k:Int) : RedundantTimeList =
    choose((res:RedundantTimeList) => isInced(l,k,res))

}
