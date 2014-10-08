/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Trees.Expr

class Example(val ins: Seq[Expr])
case class InOutExample(is: Seq[Expr], val outs: Seq[Expr]) extends Example(is)
case class InExample(is: Seq[Expr]) extends Example(is)
