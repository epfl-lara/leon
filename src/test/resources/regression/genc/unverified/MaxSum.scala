/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

/* VSTTE 2010 challenge 1 */

object MaxSum {

  def maxSum(a: Array[Int]): (Int, Int) = ({
    require(a.length >= 0 && isPositive(a))
    var sum = 0
    var max = 0
    var i = 0
    (while(i < a.length) {
      if(max < a(i))
        max = a(i)
      sum = sum + a(i)
      i = i + 1
    }) invariant (sum <= i * max && i >= 0 && i <= a.length)
    (sum, max)
  }) ensuring(res => res._1 <= a.length * res._2)


  def isPositive(a: Array[Int]): Boolean = {
    require(a.length >= 0)
    def rec(i: Int): Boolean = {
      require(i >= 0)
      if(i >= a.length)
        true
      else {
        if(a(i) < 0)
          false
        else
          rec(i+1)
      }
    }
    rec(0)
  }

  def summ(to : Int): Int = ({
    require(to >= 0)
    var i = 0
    var s = 0
    (while (i < to) {
      s = s + i
      i = i + 1
    }) invariant (s >= 0 && i >= 0 && s == i*(i-1)/2 && i <= to)
    s
  }) ensuring(res => res >= 0 && res == to*(to-1)/2)


  def sumsq(to : Int): Int = ({
    require(to >= 0)
    var i = 0
    var s = 0
    (while (i < to) {
      s = s + i*i
      i = i + 1
    }) invariant (s >= 0 && i >= 0 && s == (i-1)*i*(2*i-1)/6 && i <= to)
    s
  }) ensuring(res => res >= 0 && res == (to-1)*to*(2*to-1)/6)

  def main = {
    val a = Array(1, 4, 6, 0, 234, 999)
    val sm = maxSum(a)
    val sum = sm._1
    val max = sm._2
    if (sum == 1244 && max == 999) 0
    else -1
  } ensuring { _ == 0 }

}

