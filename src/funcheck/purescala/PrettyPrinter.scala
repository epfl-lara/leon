package funcheck.purescala

import Trees._
import Common._

object PrettyPrinter {
  def apply(tree: Expr): String = {
    val retSB = pp(tree, new StringBuffer)
    retSB.toString
  }

  import java.lang.StringBuffer

  private def pp(tree: Expr, sb: StringBuffer): StringBuffer = tree match {
    case And(exprs) => {
      var nsb = sb
      nsb.append("(")
      val sz = exprs.size
      var c = 0
      exprs.foreach(ex => { nsb = pp(ex, nsb) ; c += 1 ; if(c < sz) nsb.append(" \u2227 ") })
      nsb.append(")")
      nsb
    }

    case Or(exprs) => {
      var nsb = sb
      nsb.append("(")
      val sz = exprs.size
      var c = 0
      exprs.foreach(ex => { nsb = pp(ex, nsb) ; c += 1 ; if(c < sz) nsb.append(" \u2228 ") })
      nsb.append(")")
      nsb
    }

    case Not(expr) => {
      sb.append("\u00AC(")
      pp(expr, sb)
      sb.append(")")
    }

    case IntLiteral(v) => sb.append(v)

    case BooleanLiteral(v) => sb.append(v)

    case _ => sb.append("?")
  }

}
