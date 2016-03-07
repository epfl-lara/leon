/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object AbsFun {


  def isPositive(a : Array[Int], size : Int) : Boolean = {
    require(a.length >= 0 && size <= a.length)
    rec(0, a, size)
  }

  def rec(i: Int, a: Array[Int], size: Int) : Boolean = {
    require(a.length >= 0 && size <= a.length && i >= 0)

    if(i >= size) true
    else {
      if (a(i) < 0)
        false
      else
        rec(i + 1, a, size)
    }
  }

  // Returning Arrays is not supported by GenC
  def abs(tab: Array[Int]): Array[Int] = {
    require(tab.length >= 0)
    val t = while0(Array.fill(tab.length)(0), 0, tab)
    t._1
  } ensuring(res => isPositive(res, res.length))


  def while0(t: Array[Int], k: Int, tab: Array[Int]): (Array[Int], Int) = {
    require(tab.length >= 0 &&
            t.length == tab.length &&
            k >= 0 &&
            k <= tab.length &&
            isPositive(t, k))

    if(k < tab.length) {
      val nt = if(tab(k) < 0) {
        t.updated(k, -tab(k))
      } else {
        t.updated(k, tab(k))
      }
      while0(nt, k+1, tab)
    } else {
      (t, k)
    }
  } ensuring(res =>
      res._2 >= tab.length &&
      res._1.length == tab.length &&
      res._2 >= 0 &&
      res._2 <= tab.length &&
      isPositive(res._1, res._2))

  def property(t: Array[Int], k: Int): Boolean = {
    require(isPositive(t, k) && t.length >= 0 && k >= 0)
    if(k < t.length) {
      val nt = if(t(k) < 0) {
        t.updated(k, -t(k))
      } else {
        t.updated(k, t(k))
      }
      isPositive(nt, k+1)
    } else true
  } holds
}
