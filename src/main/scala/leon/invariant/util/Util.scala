package leon
package invariant.util

import purescala.Expressions._
import purescala.Types._
import purescala.PrettyPrintable
import purescala.PrinterContext
import purescala.PrinterHelpers._

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
}
