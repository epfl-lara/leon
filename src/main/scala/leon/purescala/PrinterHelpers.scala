/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import purescala.Common._
import purescala.Types._
import purescala.Definitions._

object PrinterHelpers {
  implicit class Printable(val f: PrinterContext => Any) extends AnyVal {
    def print(ctx: PrinterContext) = f(ctx)
  }

  implicit class PrintingHelper(val sc: StringContext) extends AnyVal {

    def p(args: Any*)(implicit ctx: PrinterContext): Unit = {
      val printer = ctx.printer
      val sb      = printer.sb

      val strings     = sc.parts.iterator
      val expressions = args.iterator

      var extraInd = 0
      var firstElem = true

      while(strings.hasNext) {
        val s = strings.next.stripMargin

        // Compute indentation
        val start = s.lastIndexOf('\n')
        if(start >= 0 || firstElem) {
          var i = start+1
          while(i < s.length && s(i) == ' ') {
            i += 1
          }
          extraInd = (i-start-1)/2
        }

        firstElem = false

        // Make sure new lines are also indented
        sb.append(s.replaceAll("\n", "\n"+("  "*ctx.lvl)))

        var nctx = ctx.copy(lvl = ctx.lvl + extraInd)

        if (expressions.hasNext) {
          val e = expressions.next

          e match {
            case (t1, t2) =>
              nary(Seq(t1, t2), " -> ").print(nctx)

            case ts: Seq[Any] =>
              nary(ts).print(nctx)

            case t: Tree =>
              val nctx2 = nctx.copy(parents = nctx.current :: nctx.parents, current = t)
              printer.pp(t)(nctx2)

            case p: Printable =>
              p.print(nctx)

            case e =>
              sb.append(e.toString)
          }
        }
      }
    }
  }

  def nary(ls: Seq[Any], sep: String = ", "): Printable = {
    val strs = List("") ::: List.fill(ls.size-1)(sep)

    implicit pctx: PrinterContext =>
      new StringContext(strs: _*).p(ls: _*)
  }

  def typed(t: Tree with Typed): Printable = {
    implicit pctx: PrinterContext =>
      p"$t : ${t.getType}"
  }

  def typed(ts: Seq[Tree with Typed]): Printable = {
    nary(ts.map(typed))
  }
}
