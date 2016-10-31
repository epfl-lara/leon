package leon
package grammars
package enumerators

import purescala.Expressions.Expr
import purescala.Types.{BooleanType, TypeTree}

object ProbwiseTopdownEnumerator {

  def main(args: Array[String]): Unit = {
    val ctx = Main.processOptions(List())

    type LabelType = TypeTree
    val grammar: LabelType => Seq[ProductionRule[LabelType, Expr]] =
      typeTree => BaseGrammar.computeProductions(typeTree)(ctx)
    def nthor(label: LabelType): Double = Math.log(grammar(label).size)
    val expansionIterator = ProbwiseTopdownEnumerator.iterator(BooleanType, grammar, nthor)

    var maxProdSize = 0
    for (i <- 1 to 1000000) {
      val next = expansionIterator.next
      assert(next ne null)
      // println(s"${next.expansion}: ${next.cost}")

      if (next.expansion.size > maxProdSize /* || i % 1000 == 0 */ ) {
        println(s"${i}: (Size: ${next.expansion.size}, Expr: ${next.expansion.produce}, Cost: ${next.cost})")
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
          println(s"Worklist size: ${worklist.size}")
          lastPrint = worklist.size
        }
      }

      val ans = worklist.dequeue
      //assert(ans.cost + 1.0e-6 >= prevAns.cost)
      //assert(ans.horizon <= 1.0e-6)
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
        //val totalWeight = prodRules.map(_.weight).sum
        //val logTotalWeight = Math.log(totalWeight)
        for (rule <- prodRules) yield {
          val expansion = ProdRuleInstance(nt,
                                           rule,
                                           rule.subTrees.map(ntChild => NonTerminalInstance[NT, R](ntChild)).toList)
          val minusLogProbPrime = minusLogProb - rule.weight //+ logTotalWeight - Math.log(rule.weight)
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

}