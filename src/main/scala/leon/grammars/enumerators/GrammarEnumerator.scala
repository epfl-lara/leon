package leon
package grammars
package enumerators

import purescala.Expressions.Expr
import utils.Interruptible

import scala.collection.mutable
import scala.collection.mutable.{HashMap, HashSet, Queue => MutableQueue}

trait GrammarEnumerator extends Interruptible {
  protected val grammar: ExpressionGrammar

  /** Returns the iterator of elements corresponding to a specific nonterminal */
  def iterator(l: Label): Iterator[Expr]
}

object GrammarEnumerator {

  private def allNTs[NT, R](nt: NT, grammar: NT => Seq[ProductionRule[NT, R]]): Set[NT] = {
    val ans = new HashSet[NT]()
    val queue = new MutableQueue[NT]()

    ans += nt
    queue += nt
    while (queue.nonEmpty) {
      val head = queue.dequeue()
      val newNTs = grammar(head).flatMap(_.subTrees).filterNot(ans).toSet
      ans ++= newNTs
      queue ++= newNTs
    }

    ans.toSet
  }

  // given a grammar: NT -> Seq[ProdRule], and a start symbol st (just to initialize the grammar),
  // compute, for each nonterminal nt, a pair (Option[ProdRule], Double):
  // Which production rule to fire to expand to the minimum cost for a tree of nt, and what is the minimum cost.
  def horizonMap[NT, R](nt: NT, grammar: NT => Seq[ProductionRule[NT, R]]): Map[NT, (Option[ProductionRule[NT, R]], Double)] = {
    type Rule = ProductionRule[NT, R]
    val all = allNTs(nt, grammar)

    val bestCosts = HashMap[NT, (Option[Rule], Double)]()

    all foreach { nt => bestCosts += (nt -> (None, Double.NegativeInfinity)) }

    val revDeps = HashMap[NT, Seq[NT]]().withDefaultValue(Seq())

    all foreach { nt =>
      val rules = grammar(nt)
      val subs = rules.flatMap(_.subTrees).toSet
      subs foreach { sub => revDeps(sub) +:= nt }
    }

    val workSet = HashSet[NT]()

    def recalculate(nt: NT): Unit = {
      def cost(rule: Rule) = rule.logProb + rule.subTrees.map(sub => bestCosts(sub)._2).sum
      workSet -= nt
      val newBest = grammar(nt).map(rule => Some(rule) -> cost(rule)).maxBy(_._2)
      if (newBest._2 > bestCosts(nt)._2) {
        bestCosts(nt) = newBest
        workSet ++= revDeps(nt)
      }
    }

    workSet ++= all.filter(grammar(_).exists(_.isTerminal))

    while (workSet.nonEmpty) recalculate(workSet.head)

    bestCosts.toMap

  }

}






















