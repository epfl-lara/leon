package leon
package grammars

/**
 * Represents a (partial) expansion of the rules of the grammar
 * @param nt: Non-terminal being expanded at the head
 * @tparam NT The type of non-terminal symbols of the grammar
 * @tparam R The type of syntax trees of the grammar
 */
sealed abstract class Expansion[NT, R](val nt: NT) {

  /** Indicates whether the expansion is complete, or whether unexpanded non-terminals still exist. */
  def complete: Boolean

  /**
   * Produces the expansion.
   * @throws `NoSuchElementException` if the expansion is not complete
   */
  def produce: R

  /**
   * Size of the expansion
   */
  def size: Int

  /**
   * Computes the ``horizon'' of this partial expansion. The horizon is the minimum extra negative log probability of
   * all completed extensions of this expansion.
   * @param grammar The grammar
   * @param nthor The horizon of each non-terminal
   */
  def horizon(nthor: NT => Double): Double

}

case class NonTerminalInstance[NT, R](override val nt: NT) extends Expansion[NT, R](nt) {
  override val complete: Boolean = false
  override def produce: R = throw new NoSuchElementException(s"Unable to expand non-terminal ${this}")
  override val size: Int = 1
  override def horizon(nthor: NT => Double): Double = nthor(nt)
}

case class ProdRuleInstance[NT, R](
    override val nt: NT,
    rule: ProductionRule[NT, R],
    children: List[Expansion[NT, R]]
) extends Expansion[NT, R](nt) {

  require(children.map(_.nt) == rule.subTrees)
  override val complete: Boolean = children.forall(_.complete)
  override def produce: R = rule.builder(children.map(_.produce))
  override val size: Int = 1 + children.map(_.size).sum
  override def horizon(nthor: NT => Double): Double = children.map(c => c.horizon(nthor)).sum

}

object Expansion {

  

}
