/* Copyright 2009-2013 EPFL, Lausanne */

package leon.synthesis.search

trait Cost extends Ordered[Cost] {
  def +(that: Cost): Cost = CostFixed(value + that.value)

  def value: Int

  def compare(that: Cost) = this.value - that.value
}

case class CostFixed(value: Int) extends Cost

object Cost {
  val zero: Cost = new CostFixed(0)
}

