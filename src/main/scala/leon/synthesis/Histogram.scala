/* Copyright 2009-2014 EPFL, Lausanne */

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
    var i = 0;
    while(i < bound) {
      var j = 0;
      while(j <= i) {

        val v1 = (this.values(j) * that.values(i-j))
        val v2 = a(i)

        a(i) = v1+v2 - (v1*v2)

        j += 1
      }
      i += 1
    }

    new Histogram(bound, a)
  }

  /**
   * hist1(c) || hist2(c) == hist1(c)+hist2(c) - hist1(c)*hist2(c)
   */
  def or(that: Histogram): Histogram = {
    val a = Array.fill(bound)(0d)
    var i = 0;
    while(i < bound) {
      val v1 = this.values(i)
      val v2 = that.values(i)

      a(i) = v1+v2 - (v1*v2)
      i += 1
    }

    new Histogram(bound, a)
  }

  lazy val maxInfo = {
    var max    = 0d;
    var argMax = -1;
    var i      = 0;
    while(i < bound) {
      if ((argMax < 0) || values(i) > max) {
        argMax = i;
        max = values(i)
      }
      i += 1;
    }
    (max, argMax)
  }

  def isImpossible  = maxInfo._1 == 0

  /**
   * Should return v<0 if `this` < `that`, that is, `this` represents better
   * solutions than `that`.
   */
  def compare(that: Histogram) = {
    val (m1, am1) = this.maxInfo
    val (m2, am2) = that.maxInfo

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

  override def toString: String = {
    var printed = 0
    val info = for (i <- 0 until bound if values(i) != 0 && printed < 5) yield {
      f"$i%2d -> ${values(i)}%,3f"
    }
    val (m,am) = maxInfo

    "H("+m+"@"+am+": "+info.mkString(", ")+")"
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

  def point(bound: Int, at: Int, v: Int) = {
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
