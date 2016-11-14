package leon
package grammars
package enumerators

import purescala.Expressions.Expr

import scala.collection.mutable.{HashMap, Queue => MutableQueue, HashSet}

trait GrammarEnumerator {
  protected val grammar: ExpressionGrammar

  /** Returns the iterator of elements corresponding to a specific nonterminal */
  def iterator(l: Label): Iterator[(Expr, Double)]
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

object Tester {
  /********** TEST CODE **********/
  import leon.frontends.scalac.ExtractionPhase
  import leon.synthesis.{SynthesisSettings, SynthesisContext}
  import leon.utils.PreprocessingPhase
  import leon.purescala.Types._

  def main(args: Array[String]) = {
    val pipeline =  ExtractionPhase andThen new PreprocessingPhase
    implicit val (ctx, program) = pipeline.run(
      LeonContext.empty,
      List("/home/koukouto/Documents/Leon/testcases/synthesis/userdefined/Grammar.scala")
    )
    val fd = program.definedFunctions.find(_.id.name == "max").get
    val sctx = new SynthesisContext(ctx, SynthesisSettings(), fd, program)
    val grammar = UserDefinedGrammar(sctx, program, Some(fd), fd.paramIds)
    val labels = List(IntegerType, BooleanType) map (Label(_, List()))//aspects.Tagged(Tags.Top, 0, None))))
    val bottomUp = new ProbwiseBottomupEnumerator(grammar, labels(0)).iterator(labels(0))
    val topDown = new ProbwiseTopdownEnumerator(grammar, labels(0), _ => (0, 0)).iterator(labels(0))
    grammar.printProductions(println)
    val before = System.currentTimeMillis()

    val b0 = for(_ <- 1 to 100) yield bottomUp.next
    val t0 = for(_ <- 1 to 100) yield topDown.next
    b0 zip t0 foreach { case ((b1, b2), (t1, t2)) =>
      println(f"$b1%60s: $b2%3.3f vs $t1%60s: $t2%3.3f")
    }

    //for (label <- labels; i <- 1 to 10 ) {
    //  val it = bottomUp.iterator(label)
    //  if (it.hasNext) {
    //    val (e, prob) = it.next
    //    //if (i%20000 == 0) println(f"$i: ${e.asString}%40s: $prob")
    //    println(f"${e.asString}%40s: $prob")
    //  }
    //}
    //println(s"Time: ${System.currentTimeMillis() - before}")
  }
}