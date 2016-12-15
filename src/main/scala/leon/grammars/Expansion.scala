package leon
package grammars

import leon.purescala.Common.FreshIdentifier
import leon.purescala.Expressions.{Expr, Terminal}
import leon.purescala.{PrettyPrintable, PrinterContext}
import leon.purescala.Types.TypeTree

/**
 * Represents a (partial) expansion of the rules of the grammar
 *
 * @param nt: Non-terminal being expanded at the head
 * @tparam NT The type of non-terminal symbols of the grammar
 * @tparam R The type of syntax trees of the grammar
 */
sealed abstract class Expansion[NT, R](val nt: NT) {

  /** Indicates whether the expansion is complete, or whether unexpanded non-terminals still exist. */
  def complete: Boolean

  /**
   * Produces the expansion.
    *
    * @throws `UnsupportedOperationException` if the expansion is not complete
   */
  def produce: R
  def falseProduce(ntWrap: NonTerminalInstance[NT, R] => R): R
  /**
   * Size of the expansion
   */
  def size: Int

  /**
    * Computes the ``horizon'' of this partial expansion. The horizon is the minimum extra log probability of all
    * completed extensions of this expansion.
    * @param nthor The horizon of each non-terminal
    */
  def horizon(nthor: NT => Double): Double

}

case class NonTerminalInstance[NT, R](override val nt: NT) extends Expansion[NT, R](nt) {
  val complete: Boolean = false
  def produce: R = throw new UnsupportedOperationException(s"Unable to expand non-terminal ${this}")
  def falseProduce(ntWrap: NonTerminalInstance[NT, R] => R): R = ntWrap(this)
  val size: Int = 1
  def horizon(nthor: NT => Double): Double = nthor(nt)
}

case class ProdRuleInstance[NT, R](
  override val nt: NT,
  rule: ProductionRule[NT, R],
  children: List[Expansion[NT, R]]
) extends Expansion[NT, R](nt) {

  require(children.map(_.nt) == rule.subTrees)
  val complete: Boolean = children.forall(_.complete)
  def produce: R = rule.builder(children.map(_.produce))
  override def falseProduce(ntWrap: NonTerminalInstance[NT, R] => R): R = {
    rule.builder(children.map(_.falseProduce(ntWrap)))
  }
  val size: Int = 1 + children.map(_.size).sum
  def horizon(nthor: NT => Double): Double = children.map(c => c.horizon(nthor)).sum
}

/**
  * Proxy class that allows us to treat instances of Expansion[NT, Expr] as instances of Expr. This is useful, for
  * example, in partial evaluation
  *
  * @param expansion The expansion being wrapped
  */
case class ExpansionExpr(expansion: Expansion[Label, Expr])
  extends Expr with Terminal with PrettyPrintable {

  def getType: TypeTree = {
    expansion.nt.getType
  }

  override def printWith(implicit pctx: PrinterContext): Unit = {
    import leon.purescala.PrinterHelpers._
    p"$expansion"
  }

  override def isSimpleExpr = true

  override def toString = try {
    expansion.produce.toString
  } catch {
    case _: UnsupportedOperationException =>
      val tp = expansion.nt.getType
      FreshIdentifier(Console.BOLD + tp.toString + Console.RESET, tp).toVariable.toString
  }

}
