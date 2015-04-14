/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Expressions._
import leon.utils.ASCIIHelpers._

class Example(val ins: Seq[Expr])
case class InOutExample(is: Seq[Expr], outs: Seq[Expr]) extends Example(is)
case class InExample(is: Seq[Expr]) extends Example(is)

class ExamplesTable(title: String, ts: Seq[Example]) {
  override def toString = {
    var tt = new Table(title)

    for (t <- ts) {
      val os = t match {
        case InOutExample(_, outs) =>
          outs.map(Cell(_))
        case _ =>
          Seq(Cell("?"))
      }

      tt += Row(
        t.ins.map(Cell(_)) ++ Seq(Cell("->")) ++ os
      )
    }

    tt.render
  }

}

