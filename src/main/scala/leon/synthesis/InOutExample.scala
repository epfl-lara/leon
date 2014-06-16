/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Trees.Expr

case class InOutExample(ins: Seq[Expr], outs: Seq[Expr]) {
  def inExample = InExample(ins)
}


case class InExample(ins: Seq[Expr])
