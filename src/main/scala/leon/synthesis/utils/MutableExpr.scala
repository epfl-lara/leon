package leon
package synthesis.utils

import purescala.Expressions.Expr
import purescala.Extractors.Extractable
import purescala.{PrinterHelpers, PrinterContext, PrettyPrintable}

/** A mutable expression box useful for STE */
case class MutableExpr(var underlying: Expr) extends Expr with Extractable with PrettyPrintable {
  def getType = underlying.getType

  def extract: Option[(Seq[Expr], (Seq[Expr]) => Expr)] = Some(
    Seq(underlying),
    { case Seq(e) => new MutableExpr(e) }
  )

  override def printWith(implicit pctx: PrinterContext): Unit = {
    import PrinterHelpers._
    p"$underlying"
  }
}
