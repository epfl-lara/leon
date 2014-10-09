/* Copyright 2009-2014 EPFL, Lausanne */

package leon.synthesis

class Distribution(val span: Int, val values: Array[Long], val total: Long) extends Ordered[Distribution] {
  def and(that: Distribution): Distribution = { val res = (this, that) match {
    case (d1, d2) if d1.total == 0 =>
      d1

    case (d1, d2) if d2.total == 0 =>
      d2

    case (d1: PointDistribution, d2: PointDistribution) =>
      if (d1.at + d2.at >= span) {
        Distribution.empty(span)
      } else {
        new PointDistribution(span, d1.at+d2.at)
      }

    case (d: PointDistribution, o) =>
      val a   = Array.fill(span)(0l)

      val base = d.at
      var innerTotal = 0l;
      var i    = d.at;
      while(i < span) {
        val v = o.values(i-base)
        a(i) = v
        innerTotal += v
        i += 1
      }

      if (innerTotal == 0) {
        Distribution.empty(span)
      } else {
        new Distribution(span, a, total)
      }

    case (o, d: PointDistribution) =>
      val a   = Array.fill(span)(0l)

      val base = d.at
      var innerTotal = 0l;
      var i    = d.at;
      while(i < span) {
        val v = o.values(i-base)
        a(i) = v
        innerTotal += v
        i += 1
      }

      if (innerTotal == 0) {
        Distribution.empty(span)
      } else {
        new Distribution(span, a, total)
      }

    case (left, right) =>
      if (left == right) {
        left
      } else {
        val a   = Array.fill(span)(0l)
        var innerTotal = 0l;
        var i = 0;
        while (i < span) {
          var j = 0;
          while (j < span) {
            if (i+j < span) {
              val lv = left.values(i)
              val rv = right.values(j)

              a(i+j) += lv*rv
              innerTotal += lv*rv
            }
            j += 1
          }
          i += 1
        }

        if (innerTotal == 0) {
          Distribution.empty(span)
        } else {
          new Distribution(span, a, left.total * right.total)
        }
      }
  }
    //println("And of "+this+" and "+that+" = "+res)
    res
  }

  def or(that: Distribution): Distribution = (this, that) match {
    case (d1, d2) if d1.total == 0 =>
      d2

    case (d1, d2) if d2.total == 0 =>
      d1

    case (d1: PointDistribution, d2: PointDistribution) =>
      if (d1.at < d2.at) {
        d1
      } else {
        d2
      }

    case (d1, d2) =>
      if (d1.weightedSum < d2.weightedSum) {
      //if (d1.firstNonZero < d2.firstNonZero) {
        d1
      } else {
        d2
      }
  }

  lazy val firstNonZero: Int = {
    if (total == 0) {
      span
    } else {
      var i = 0;
      var continue = true;
      while (continue && i < span) {
        if (values(i) != 0l) {
          continue = false
        }
        i += 1
      }
      i
    }
  }

  lazy val weightedSum: Double = {
    var res = 0d;
    var i = 0;
    while (i < span) {
      res += (1d*i*values(i))/total
      i += 1
    }
    res
  }

  override def toString: String = {
    "Tot:"+total+"(at "+firstNonZero+")"
  }

  def compare(that: Distribution) = {
    this.firstNonZero - that.firstNonZero
  }
}

object Distribution {
  def point(span: Int, at: Int) = {
    if (span <= at) {
      empty(span)
    } else {
      new PointDistribution(span, at)
    }
  }

  def empty(span: Int)               = new Distribution(span, Array[Long](), 0l)
  def uniform(span: Int, v: Long, total: Int) = {
    new Distribution(span, Array.fill(span)(v), total)
  }

  def uniformFrom(span: Int, from: Int, ratio: Double) = {
    var i = from
    val a = Array.fill(span)(0l)
    while(i < span) {
      a(i) = 1
      i += 1
    }
    
    new Distribution(span, a, ((span-from).toDouble*(1/ratio)).toInt)
  }
}

class PointDistribution(span: Int, val at: Int) extends Distribution(span, new Array[Long](span).updated(at, 1l), 1l) {
  override lazy val firstNonZero: Int = {
    at
  }
}
