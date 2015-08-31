/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import leon.purescala.{PrinterContext, PrettyPrintable}
import leon.purescala.PrinterHelpers._
import purescala.Types._
import purescala.Expressions._

// Corresponds to a smt map, not a leon/scala array
private[solvers] case class RawArrayType(from: TypeTree, to: TypeTree) extends TypeTree with PrettyPrintable {
  override def printWith(implicit pctx: PrinterContext): Unit = {
    p"RawArrayType[$from, $to]"
  }
}

// Corresponds to a raw array value, which is coerced to a Leon expr depending on target type (set/array)
private[solvers] case class RawArrayValue(keyTpe: TypeTree, elems: Map[Expr, Expr], default: Expr) extends Expr with PrettyPrintable{
  val getType = RawArrayType(keyTpe, default.getType)

  override def printWith(implicit pctx: PrinterContext): Unit = {
    p"RawArrayValue[$keyTpe](${nary(elems.toSeq, ", ")}, default = $default)"
  }
}
