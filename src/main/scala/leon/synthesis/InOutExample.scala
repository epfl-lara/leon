/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Expressions._
import leon.utils.ASCIIHelpers._

class Example(val ins: Seq[Expr])
case class InOutExample(is: Seq[Expr], outs: Seq[Expr]) extends Example(is)
case class InExample(is: Seq[Expr]) extends Example(is)
