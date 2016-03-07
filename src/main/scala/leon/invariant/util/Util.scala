/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.util

import purescala.Expressions._
import purescala.Types._
import purescala.PrettyPrintable
import purescala.PrinterContext
import purescala.PrinterHelpers._
import purescala.Definitions._
import purescala.Common._
import purescala.ExprOps._

object FileCountGUID {
  var fileCount = 0
  def getID: Int = {
    val oldcnt = fileCount
    fileCount += 1
    oldcnt
  }
}

//three valued logic
object TVL {
  abstract class Value
  object FALSE extends Value
  object TRUE extends Value
  object MAYBE extends Value
}

//this is used as a place holder for result
case class ResultVariable(tpe: TypeTree) extends Expr with Terminal with PrettyPrintable {
  val getType = tpe
  override def toString: String = "#res"

  def printWith(implicit pctx: PrinterContext) = {
    p"#res"
  }
}

object Util {

  val zero = InfiniteIntegerLiteral(0)
  val one = InfiniteIntegerLiteral(1)
  val mone = InfiniteIntegerLiteral(-1)
  val bone = BigInt(1)
  val tru = BooleanLiteral(true)
  val fls = BooleanLiteral(false)

  def fix[A](f: (A) => A)(a: A): A = {
    val na = f(a)
    if (a == na) a else fix(f)(na)
  }

  def gcd(x: Int, y: Int): Int = {
    if (x == 0) y
    else gcd(y % x, x)
  }

  /**
   * A cross product with an optional filter
   */
  def cross[U, V](a: Set[U], b: Set[V], selector: Option[(U, V) => Boolean] = None): Set[(U, V)] = {

    val product = (for (x <- a; y <- b) yield (x, y))
    if (selector.isDefined)
      product.filter(pair => selector.get(pair._1, pair._2))
    else
      product
  }

  /**
   * Transitively close the substitution map from identifiers to expressions.
   * Note: the map is required to be acyclic.
   */
  def substClosure(initMap: Map[Identifier, Expr]): Map[Identifier, Expr] = {
    if (initMap.isEmpty) initMap
    else {
      var stables = Seq[(Identifier, Expr)]()
      var unstables = initMap.toSeq
      var changed = true
      while (changed) {
        changed = false
        var foundStable = false
        unstables = unstables.flatMap {
          case (k, v) if variablesOf(v).intersect(initMap.keySet).isEmpty =>
            foundStable = true
            stables +:= (k -> v)
            Seq()
          case (k, v) =>
            changed = true
            Seq((k -> replaceFromIDs(initMap, v)))
        }
        if (!foundStable)
          throw new IllegalStateException(s"No stable entry was found in the map! The map is possibly cyclic: $initMap")
      }
      stables.toMap
    }
  }
}
