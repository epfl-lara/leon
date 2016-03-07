/* Copyright 2009-2016 EPFL, Lausanne */

package leon.synthesis

/**
 * Histogram from 0 to `bound`, each value between 0 and 1
 * hist(c) = v means we have a `v` likelihood of finding a solution of cost `c`
 */
class Histogram(val bound: Int, val values: Array[Double]) extends Ordered[Histogram] {
  /**
   */
  def and(that: Histogram): Histogram = {
    val a = Array.fill(bound)(0d)
    var i = 0
    while(i < bound) {
      var j = 0
      while(j <= i) {

        val v1 = this.values(j) * that.values(i - j)
        val v2 = a(i)

        a(i) = v1+v2 - (v1*v2)

        j += 1
      }
      i += 1
    }

    val res = new Histogram(bound, a)
    println("==== && ====")
    println("this:"+ this)
    println("that:"+ that)
    println(" ==> "+res)
    res
  }

  /**
   * hist1(c) || hist2(c) == hist1(c)+hist2(c) - hist1(c)*hist2(c)
   */
  def or(that: Histogram): Histogram = {
    val a = Array.fill(bound)(0d)
    var i = 0
    while(i < bound) {
      val v1 = this.values(i)
      val v2 = that.values(i)

      a(i) = v1+v2 - (v1*v2)
      i += 1
    }

    val res = new Histogram(bound, a)
    println("==== || ====")
    println("this:"+ this)
    println("that:"+ that)
    println(" ==> "+res)
    res
  }

  lazy val mode = {
    var max    = 0d
    var argMax = -1
    var i      = 0
    while(i < bound) {
      if ((argMax < 0) || values(i) > max) {
        argMax = i
        max = values(i)
      }
      i += 1
    }
    (max, argMax)
  }

  lazy val firstNonZero = {
    var i      = 0
    var mini   = -1
    while(i < bound && mini < 0) {
      if (values(i) > 0) {
        mini = i
      }
      i += 1
    }
    if (mini >= 0) {
      (values(mini), mini)
    } else {
      (0d, bound)
    }
  }

  lazy val moment = {
    var i      = 0
    var moment = 0d
    var allV   = 0d
    while(i < bound) {
      val v = values(i)
      moment += v*i
      allV   += v
      i += 1
    }

    moment/allV
  }

  def isImpossible  = mode._1 == 0

  def compareByMode(that: Histogram) = {
    val (m1, am1) = this.mode
    val (m2, am2) = that.mode

    if (m1 == m2) {
      am1 - am2
    } else {
      if (m2 < m1) {
        -1
      } else if (m2 == m1) {
        0
      } else {
        +1
      }
    }
  }

  def rescaled(by: Double): Histogram = {
    val a = new Array[Double](bound)

    var i = 0
    while(i < bound) {
      val v = values(i)
      
      val nv = 1-Math.pow(1-v, by)

      a(i) = nv

      i += 1
    }

    new Histogram(bound, a)
  }

  def compareByFirstNonZero(that: Histogram) = {
    this.firstNonZero._2 - that.firstNonZero._2
  }

  def compareByMoment(that: Histogram) = {
    this.moment - that.moment
  }

  /**
   * Should return v<0 if `this` < `that`, that is, `this` represents better
   * solutions than `that`.
   */
  def compare(that: Histogram) = {
    compareByFirstNonZero(that)
  }

  override def toString: String = {
    var lastv = -1d
    var fromi = -1
    val entries = new scala.collection.mutable.ArrayBuffer[((Int, Int), Double)]()


    for (i <- 0 until bound) {
      val v = values(i)
      if (lastv < 0) {
        lastv = v
        fromi = i
      }

      if (lastv != v) {
        entries += (fromi, i-1) -> lastv
        lastv = v
        fromi = i
      }
    }
    entries += (fromi, bound-1) -> lastv

    val info = for (((from, to), v) <- entries) yield {
      val k = if (from == to) {
        s"$from"
      } else {
        s"$from..$to"
      }

      f"$k -> $v%1.3f"
    }

    s"H($summary: ${info.mkString(", ")})"
  }


  def summary: String = {
    //val (m, am) = maxInfo
    val (m, am) = firstNonZero

    f"$m%1.4f->$am%-2d ($moment%1.3f)"
  }
}

object Histogram {
  def clampV(v: Double): Double = {
    if (v < 0) {
      0d
    } else if (v > 1) {
      1d
    } else {
      v
    }
  }

  def point(bound: Int, at: Int, v: Double) = {
    if (bound <= at) {
      empty(bound)
    } else {
      new Histogram(bound, Array.fill(bound)(0d).updated(at, clampV(v)))
    }
  }

  def empty(bound: Int) = {
    new Histogram(bound, Array.fill(bound)(0d))
  }

  def uniform(bound: Int, v: Double) = {
    uniformFrom(bound, 0, v)
  }

  def uniformFrom(bound: Int, from: Int, v: Double) = {
    val vSafe = clampV(v)
    var i = from
    val a = Array.fill(bound)(0d)
    while(i < bound) {
      a(i) = vSafe
      i += 1
    }

    new Histogram(bound, a)
  }
}
