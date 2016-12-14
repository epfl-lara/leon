package leon
package grammars
package enumerators

import purescala.Expressions.Expr

import scala.collection.mutable.{HashMap, HashSet, Queue => MutableQueue}

trait GrammarEnumerator {
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

  def horizonMap[NT, R](nt: NT, grammar: NT => Seq[ProductionRule[NT, R]]): Map[NT, (Option[ProductionRule[NT, R]], Double)] = {
    val map = new HashMap[NT, (Option[ProductionRule[NT, R]], Double)]()
    val ntSet = allNTs(nt, grammar)
    ntSet.foreach(ntPrime => map.put(ntPrime, (None, Double.NegativeInfinity)))

    def relax(ntPrime: NT): Boolean = {
      require(map.contains(ntPrime))

      var newProb = map(ntPrime)
      for (rule <- grammar(ntPrime)) {
        var ruleLogProb = rule.weight
        for (childNT <- rule.subTrees) {
          ruleLogProb = ruleLogProb + map(childNT)._2
        }
        if (ruleLogProb > newProb._2) newProb = (Some(rule), ruleLogProb)
      }
      val ans = map(ntPrime)._2 < newProb._2
      if (ans) map.put(ntPrime, newProb)
      ans
    }

    while(ntSet exists relax) {}

    map.toMap
  }

}