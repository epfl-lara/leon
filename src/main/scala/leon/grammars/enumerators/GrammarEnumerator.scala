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
  // TODO: Document algorithm
  def horizonMap[NT, R](nt: NT, grammar: NT => Seq[ProductionRule[NT, R]]): Map[NT, (Option[ProductionRule[NT, R]], Double)] = {
    import leon.utils.MapUtils.seqToMap
    type Rule = ProductionRule[NT, R]

    val committed = HashMap[NT, (Rule, Double)]()

    val queue = new mutable.PriorityQueue[(NT, Rule, Double)]()(Ordering.by(_._3))

    val all = allNTs(nt, grammar).toSeq

    val rulesToNTs = seqToMap(
      for {
        nt   <- all
        rule <- grammar(nt)
      } yield rule -> nt
    )

    val revDeps: Map[NT, Seq[Rule]] = seqToMap(
      for {
        nt   <- all
        rule <- grammar(nt)
        sub  <- rule.subTrees
      } yield sub -> rule
    ).withDefaultValue(Seq())

    for {
      nt   <- all
      rule <- grammar(nt)
      if rule.isTerminal
    } queue.enqueue((nt, rule, rule.logProb))

    while (queue.nonEmpty) {
      val (nt, rule, prob) = queue.dequeue()
      if (!committed.contains(nt)) {
        committed += nt -> (rule, prob)
        revDeps(nt) foreach { rule =>
          if (rule.subTrees.forall(committed.contains)) {
            val probs = rule.subTrees map (committed(_)._2)
            val prob = probs.sum + rule.logProb
            val nts = rulesToNTs(rule)
            nts foreach (nt => queue.enqueue((nt, rule, prob)))
          }
        }
      }
    }

    all.map { nt => nt -> (committed.get(nt) match {
      case Some((rule, prob)) =>
        (Some(rule), prob)
      case None =>
        (None, Double.NegativeInfinity)
    })}.toMap
  }

}






















