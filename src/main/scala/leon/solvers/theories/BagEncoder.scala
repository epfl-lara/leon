/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package theories

import purescala.Common._
import purescala.Expressions._
import purescala.Types._

object BagEncoder extends TheoryEncoder {
  val encoder = new Encoder
  val decoder = new Decoder
}
