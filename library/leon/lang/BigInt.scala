/* Copyright 2009-2016 EPFL, Lausanne */

package leon.lang

import java.lang.Integer
import leon.annotation._
import scala.Int
import scala.Predef.String

@ignore
object BigInt {
  def apply(b: Int): scala.math.BigInt = scala.math.BigInt(b)
  def apply(b: String): scala.math.BigInt = scala.math.BigInt(b)

  def unapply(b: scala.math.BigInt): scala.Option[Int] = {
    if(b >= Integer.MIN_VALUE && b <= Integer.MAX_VALUE) {
      scala.Some(b.intValue())
    } else {
      scala.None
    }
  }
}