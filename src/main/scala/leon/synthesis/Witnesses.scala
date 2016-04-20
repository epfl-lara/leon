/* Copyright 2009-2016 EPFL, Lausanne */

package leon.synthesis

import leon.purescala.Common.Identifier
import leon.purescala._
import Types._
import Extractors._
import Expressions.Expr
import PrinterHelpers._

object Witnesses {
  
  abstract class Witness extends Expr with Extractable with PrettyPrintable {
    val getType = BooleanType
    override def isSimpleExpr = true
  }
  
  case class Guide(e: Expr) extends Witness {
    def extract: Option[(Seq[Expr], Seq[Expr] => Expr)] = Some((Seq(e), (es: Seq[Expr]) => Guide(es.head)))

    override def printWith(implicit pctx: PrinterContext): Unit = {
      p"⊙{$e}"
    }
  }

  case class Terminating(fi: Expr) extends Witness {
    def extract: Option[(Seq[Expr], Seq[Expr] => Expr)] = Some(( Seq(fi), { case Seq(fi) => Terminating(fi) }))

    override def printWith(implicit pctx: PrinterContext): Unit = {
      p"↓$fi"
    }
  }

  case class Hint(e: Expr) extends Witness {
    def extract: Option[(Seq[Expr], Seq[Expr] => Expr)] = Some(( Seq(e), { case Seq(e) => Hint(e) }))

    override def printWith(implicit pctx: PrinterContext): Unit = {
      p"谶$e"
    }
  }

  case class Inactive(i: Identifier) extends Witness {
    def extract: Option[(Seq[Expr], Seq[Expr] => Expr)] = Some((Seq(), _ => this ))
    override def printWith(implicit pctx: PrinterContext): Unit = {
      p"inactive($i)"
    }

  }
}
