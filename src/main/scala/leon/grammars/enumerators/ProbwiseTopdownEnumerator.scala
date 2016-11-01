package leon
package grammars
package enumerators

import purescala.Expressions.Expr
import purescala.Types.{BooleanType, TypeTree}

import scala.collection.mutable

object ProbwiseTopdownEnumerator {

  def main(args: Array[String]): Unit = {
    implicit val ctx = Main.processOptions(List())
    def t2l(tp: TypeTree) = Label(tp, Nil)
    def nthor(label: Label): Double = Math.log(BaseGrammar.getProductions(label).size)
    val expansionIterator = ProbwiseTopdownEnumerator.iterator(t2l(BooleanType), BaseGrammar.getProductions, nthor)

    var maxProdSize = 0
    for (i <- 1 to 1000000) {
      val next = expansionIterator.next
      assert(next ne null)
      // println(s"${next.expansion}: ${next.cost}")

      if (next.expansion.size > maxProdSize /* || i % 1000 == 0 */ ) {
        println(s"$i: (Size: ${next.expansion.size}, Expr: ${next.expansion.produce}, Cost: ${next.cost})")
        maxProdSize = next.expansion.size
      }
    }
  }

  /**
   * Represents an element of the worklist
   * @param expansion The partial expansion under consideration
   * @param cost The cost already accumulated by the expansion
   * @param horizon The minimum cost that this expansion will accumulate before becoming concrete
   */
  case class WorklistElement[NT, R](
      expansion: Expansion[NT, R],
      cost: Double,
      horizon: Double
  ) {
    require(cost >= 0 && horizon >= 0)
  }

  def iterator[NT, R](
      nt: NT,
      grammar: NT => Seq[ProductionRule[NT, R]],
      nthor: NT => Double
  ) = new Iterator[WorklistElement[NT, R]](){

    type TyEl = WorklistElement[NT, R]
    val ordering = Ordering.by[TyEl, Double](elem => -(elem.cost + elem.horizon))
    val worklist = new scala.collection.mutable.PriorityQueue[TyEl]()(ordering)

    worklist.enqueue(new TyEl(NonTerminalInstance[NT, R](nt), 0.0, nthor(nt)))
    var lastPrint: Int = 1
    var prevAns = new TyEl(NonTerminalInstance[NT, R](nt), 0.0, nthor(nt))

    def hasNext: Boolean = worklist.nonEmpty

    def next: TyEl = {
      while (!worklist.head.expansion.complete) {
        val head = worklist.dequeue
        val newElems = expandNext(head, grammar, nthor)
        worklist ++= newElems
        if (worklist.size >= 1.5 * lastPrint) {
          //println(s"Worklist size: ${worklist.size}")
          lastPrint = worklist.size
        }
      }

      val ans = worklist.dequeue
      assert(ans.cost + 1.0e-6 >= prevAns.cost)
      assert(ans.horizon <= 1.0e-6)
      prevAns = ans
      ans
    }

  }

  def expandNext[NT, R](
      elem: WorklistElement[NT, R],
      grammar: NT => Seq[ProductionRule[NT, R]],
      nthor: NT => Double
  ): Seq[WorklistElement[NT, R]] = {
    val expansion = elem.expansion
    val minusLogProb = elem.cost
    val horizon = elem.horizon

    require(!expansion.complete)

    expansion match {

      case NonTerminalInstance(nt) => {
        val prodRules = grammar(nt)
        // val totalWeight = prodRules.map(_.weight).sum
        // val logTotalWeight = Math.log(totalWeight)
        for (rule <- prodRules) yield {
          val expansion = ProdRuleInstance(nt,
                                           rule,
                                           rule.subTrees.map(ntChild => NonTerminalInstance[NT, R](ntChild)).toList)
          val minusLogProbPrime = minusLogProb - rule.weight // + logTotalWeight - Math.log(rule.weight)
          val horizonPrime = rule.subTrees.map(nthor).sum
          WorklistElement(expansion, minusLogProbPrime, horizonPrime)
        }
      }

      case ProdRuleInstance(nt, rule, children) => {
        require(children.exists(!_.complete))

        def expandChildren(cs: List[Expansion[NT, R]]): Seq[(List[Expansion[NT, R]], Double)] = cs match {
          case Nil => throw new IllegalArgumentException()
          case csHd :: csTl if csHd.complete => for (csTlExp <- expandChildren(csTl))
                                                yield (csHd :: csTlExp._1, csTlExp._2)
          case csHd :: csTl => for (csHdExp <- expandNext(WorklistElement(csHd, 0.0, 0.0), grammar, nthor))
                               yield (csHdExp.expansion :: csTl, csHdExp.cost)
        }
  
        for (childExpansion <- expandChildren(children)) yield {
          val expPrime = ProdRuleInstance(nt, rule, childExpansion._1)
          val minusLogProbPrime = minusLogProb + childExpansion._2
          val horizonPrime = expPrime.horizon(nthor)
          WorklistElement[NT, R](expPrime, minusLogProbPrime, horizonPrime)
        }
      }

    }
  }

  def allNTs[NT, R](nt: NT, grammar: NT => Seq[ProductionRule[NT, R]]): Set[NT] = {
    val ans = new mutable.HashSet[NT]()
    val queue = new mutable.Queue[NT]()

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
    val map = new mutable.HashMap[NT, (Option[ProductionRule[NT, R]], Double)]()
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

    map.toMap.mapValues{ case (o, d) => (o, -d) }
  }

}