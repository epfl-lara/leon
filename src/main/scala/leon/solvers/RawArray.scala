/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import purescala.Types._
import purescala.Expressions._
import purescala.Extractors._
import purescala.TypeOps._
import purescala.{PrettyPrintable, PrinterContext}
import purescala.PrinterHelpers._

// Corresponds to a complete map (SMT Array), not a Leon/Scala array
// Only used within solvers or SMT for encoding purposes
case class RawArrayType(from: TypeTree, to: TypeTree) extends TypeTree with PrettyPrintable {
  override def asString(implicit ctx: LeonContext) = {
    s"RawArrayType[${from.asString}, ${to.asString}]"
  }

  override def printWith(implicit pctx: PrinterContext) = {
    p"RawArrayType[$from, $to]"
  }
}

// Corresponds to a raw array value, which is coerced to a Leon expr depending on target type (set/array)
case class RawArrayValue(keyTpe: TypeTree, elems: Map[Expr, Expr], default: Expr) extends Expr with Extractable with PrettyPrintable {

  override def extract: Option[(Seq[Expr], (Seq[Expr]) => Expr)] = {
    val linearized: Seq[Expr] = elems.toVector.flatMap(p => Seq(p._1, p._2)) :+ default
    Some((linearized, es => {
      val freshElems = es.dropRight(1).grouped(2).map(p => p(0) -> p(1)).toMap
      RawArrayValue(keyTpe, freshElems, es.last)
    }))
  }

  val getType = RawArrayType(keyTpe, default.getType)

  override def asString(implicit ctx: LeonContext) = {
    val elemsString = elems.map { case (k, v) => k.asString+" -> "+v.asString } mkString(", ")
    s"RawArray[${keyTpe.asString}]($elemsString, default = ${default.asString})"
  }

  def printWith(implicit pctx: PrinterContext): Unit = {
    p"RawArray[$keyTpe](${nary(elems.toSeq, ",")})(default=$default)"
  }
}

case class RawArraySelect(array: Expr, index: Expr) extends Expr with Extractable with PrettyPrintable {

  override def extract: Option[(Seq[Expr], (Seq[Expr]) => Expr)] =
    Some(Seq(array, index), es => RawArraySelect(es(0), es(1)))

  val getType = array.getType match {
    case RawArrayType(from, to) if isSubtypeOf(index.getType, from) =>
      to
    case _ =>
      Untyped
  }

  override def asString(implicit ctx: LeonContext) = {
    s"$array($index)"
  }

  override def printWith(implicit pctx: PrinterContext) = {
    p"$array($index)"
  }

}

case class RawArrayUpdated(array: Expr, index: Expr, newValue: Expr) extends Expr with Extractable with PrettyPrintable {

  val getType = array.getType

  override def extract: Option[(Seq[Expr], (Seq[Expr]) => Expr)] =
    Some((Seq(array, index, newValue), es => RawArrayUpdated(es(0), es(1), es(2))))

  override def asString(implicit ctx: LeonContext) = {
    s"$array($index) = $newValue"
  }

  override def printWith(implicit pctx: PrinterContext) = {
    p"$array($index) = $newValue"
  }

}
