package leon
package grammars
package enumerators

import purescala.Expressions.Expr
import scala.util.Try
import scala.collection.mutable.{ PriorityQueue, HashSet, Set => MutableSet, HashMap, ArrayBuffer }

/** An enumerator that jointly enumerates elements from a number of production rules by employing a bottom-up strategy.
  * After initialization, each nonterminal will produce a series of unique elements in decreasing probability order.
  *
  * @param nts A mapping from each nonterminal to the production rules corresponding to it,
  *            and the rule which corresponds to the first element
  * @tparam NT Type of the nonterminal of the production rules.
  * @tparam R The type of enumerated elements.
  */
abstract class AbstractProbwiseBottomupEnumerator[NT, R](nts: Map[NT, (ProductionRule[NT, R], Seq[ProductionRule[NT, R]])]){

  type Rule = ProductionRule[NT, R]

  class Frontier(dim: Int, rule: Rule, streams: Seq[NonTerminalStream]) {
    private val ordering = Ordering.by[FrontierElem, Double](_.logProb)
    private val queue = new PriorityQueue[FrontierElem]()(ordering)
    private var futureElems = List.empty[LazyElem]

    private val byDim = Array.fill(dim)(
      HashMap[Int, MutableSet[FrontierElem]]()
        .withDefaultValue(MutableSet[FrontierElem]())
    )

    private def dominates(e1: FrontierElem, e2: FrontierElem) =
      e1.coordinates zip e2.coordinates forall ((_: Int) <= (_: Int)).tupled

    private def enqueue(elem: FrontierElem, grownDim: Int) = {
      val elems = if (grownDim >= 0) {
        val grownTo = elem.coordinates(grownDim)
        byDim(grownDim)(grownTo)
      } else {
        MutableSet()
      }
      if (!(elems exists (dominates(_, elem)))) {
        queue += elem
        for (i <- 0 until dim) {
          val coord = elem.coordinates(i)
          byDim(i)(coord) += elem
        }
      }
    }

    def +=(l: LazyElem) = futureElems ::= l

    def elem(le: LazyElem): Option[(FrontierElem, Int)] = try {
      val children = le.coordinates.zip(streams).map { case (index, stream) => stream.get(index) }
      val (operands, logProbs) = children.unzip
      Some(FrontierElem(le.coordinates, rule.builder(operands), logProbs.sum + rule.weight), le.grownIndex)
    } catch {
      case _: UnsupportedOperationException =>
        None
    }


    private def promote() = {
      for {
        fe <- futureElems
        (elem, index) <- elem(fe)
      } enqueue(elem, index)
      futureElems = Nil
    }

    def dequeue() = {
      promote()
      val res = queue.dequeue()
      for (i <- 0 until dim)
        byDim(i)(res.coordinates(i)) -= res
      res
    }

    def headOption = {
      promote()
      queue.headOption
    }

    def isEmpty = queue.isEmpty && futureElems.isEmpty
  }

  /** An element of the frontier of an operator */
  protected case class LazyElem(coordinates: List[Int], grownIndex: Int)

  protected case class FrontierElem(coordinates: List[Int], elem: R, logProb: Double) {
    def nextElems = coordinates.zipWithIndex.map {
      case (elem, updated) => LazyElem(coordinates.updated(updated, elem + 1), updated)
    }
  }

  protected val ordering = Ordering.by[FrontierElem, Double](_.logProb)
  /** The frontier of coordinates corresponding to an operator */
  //protected type Frontier = DedupedPriorityQueue[FrontierElem]

  // The streams of elements corresponding to each nonterminal
  protected val streams: Map[NT, NonTerminalStream] =
    nts.map{ case (nt, _) => (nt, new NonTerminalStream(nt)) }

  // The operator streams per nonterminal
  protected val operators: Map[NT, Seq[OperatorStream]] =
    nts.map { case (nt, (advanced, prods)) =>
      nt -> prods.map(rule => new OperatorStream(rule, rule eq advanced))
    }

  //operators.values foreach (_.foreach(_.init()))

  /** A class that represents the stream of generated elements for a specific nonterminal. */
  protected class NonTerminalStream(val nt: NT) {
    private val buffer: ArrayBuffer[(R, Double)] = new ArrayBuffer()

    // The first element to be produced will definitely be the terminal symbol with greatest probability.
    private def init(): Unit = {
      def rec(nt: NT): (R, Double) = {
        val rule = nts(nt)._1
        val (subs, ds) = rule.subTrees.map(rec).unzip
        (rule.builder(subs), ds.sum + rule.weight)
      }
      buffer += rec(nt)
    }

    init()

    private var lock = false

    def populateNext() = !lock && {
      try {
        lock = true
        //println(s"$nt: size is ${buffer.size}, populating")
        val (r, d, op) = operators(nt).flatMap(_.getNext).maxBy(_._2)
        buffer += ((r, d))
        //println(s"$nt: Adding ($r, $d)")
        op.advance()
        lock = false
      } catch {
        case _: UnsupportedOperationException =>
      }
      !lock
    }

    @inline def get(i: Int): (R, Double) = {
      if (i == buffer.size) populateNext()
      buffer(i)
    }

    val iterator = new Iterator[(R, Double)] {
      var i = 0
      def hasNext = i < buffer.size || i == buffer.size && populateNext()
      def next = {
        val res = get(i)
        i += 1
        res
      }
    }

  }

  /** Generates elements for a specific operator */
  protected class OperatorStream(rule: ProductionRule[NT, R], isAdvanced: Boolean) {
    private val arity = rule.arity
    private val typedStreams = rule.subTrees.map(streams)
    private val frontier: Frontier = new Frontier(arity, rule, typedStreams)

    @inline def getNext: Option[(R, Double, OperatorStream)] = {
      //if (frontier.isEmpty) println(s"$rule was empty")
      frontier.headOption.map(fe => (fe.elem, fe.logProb, this))
    }

    def advance(): Unit = if (!frontier.isEmpty) {
      frontier.dequeue().nextElems foreach { frontier += _ }
    }

    private def init(): Unit = {
      frontier += LazyElem(List.fill(arity)(0), -1)
      if (isAdvanced) advance()
    }
    init()
  }

  def iterator(nt: NT) = streams.get(nt).map(_.iterator).getOrElse(Iterator())
}

class ProbwiseBottomupEnumerator(grammar: ExpressionGrammar, init: Label)(implicit ctx: LeonContext)
  extends AbstractProbwiseBottomupEnumerator[Label, Expr](ProbwiseBottomupEnumerator.productive(grammar, init))

object ProbwiseBottomupEnumerator {
  def productive(grammar: ExpressionGrammar, init: Label)(implicit ctx: LeonContext) = {
    val ntMap = ProbwiseTopdownEnumerator.horizonMap(init, grammar.getProductions).collect {
      case (l, (Some(r), d)) => l -> (r, grammar.getProductions(l))
    }
    ntMap.mapValues{ case (r, prods) => (r, prods.filter(_.subTrees forall ntMap.contains)) }
  }

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
    val fd = program.definedFunctions.find(_.id.name == "min").get
    val sctx = new SynthesisContext(ctx, SynthesisSettings(), fd, program)
    val grammar = UserDefinedGrammar(sctx, program, Some(fd), fd.paramIds)
    val labels = List(BooleanType, IntegerType) map (Label(_, List()))//aspects.Tagged(Tags.Top, 0, None))))
    val bottomUp = new ProbwiseBottomupEnumerator(grammar, labels(0))
    grammar.printProductions(println)
    val horMap = (n: Int) => ProbwiseTopdownEnumerator.horizonMap(labels(n), grammar.getProductions)
    val topDown0 = ProbwiseTopdownEnumerator.iterator[Label, Expr](labels(0),
                                                                   grammar.getProductions,
                                                                   horMap(0).mapValues(_._2))
    val topDown1 = ProbwiseTopdownEnumerator.iterator[Label, Expr](labels(1),
                                                                   grammar.getProductions,
                                                                   horMap(1).mapValues(_._2))
    val before = System.currentTimeMillis()

    val b0 = for(_ <- 1 to 100) yield bottomUp.iterator(labels(0)).next
    val t0 = for(_ <- 1 to 100) yield topDown0.next
    b0 zip t0 foreach { case (b, t) =>
      println(f"${b._1}%60s: ${b._2}%3.3f vs ${t.expansion.produce}%60s: ${t.cost}%3.3f")
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
