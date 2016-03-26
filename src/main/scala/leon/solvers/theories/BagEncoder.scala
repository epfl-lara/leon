/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package theories

import purescala.Common._
import purescala.Expressions._
import purescala.Types._

class BagEncoder(val context: LeonContext) extends TheoryEncoder {
  val encoder = new Encoder
  val decoder = new Decoder
}
