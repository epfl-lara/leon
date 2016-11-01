package leon
package grammars
package enumerators

import purescala.Expressions.Expr
import scala.collection.mutable.{ PriorityQueue, HashSet, ArrayBuffer }

/** An enumerator that jointly enumerates elements from a number of production rules by employing a bottom-up strategy.
  * After initialization, each nonterminal will produce a series of unique elements in decreasing probability order.
  *
  * @param nts A mapping from each nonterminal to the production rules corresponding to it,
  *            and the rule which corresponds to the first element
  * @tparam NT Type of the nonterminal of the production rules.
  * @tparam R The type of enumerated elements.
  */
abstract class AbstractProbwiseBottomupEnumerator[NT, R](nts: Map[NT, (ProductionRule[NT, R], Seq[ProductionRule[NT, R]])]){
  //nts.keys foreach println

  abstract class DedupedPriorityQueue[T](ord: Ordering[T]) {
    def dominates(t1: T, t2: T): Boolean
    private val underlying = new PriorityQueue[T]()(ord)
    private val elems = new HashSet[T]()

    def +=(elem: T) = {
      if (!(elems exists (dominates(_, elem)))) {
        elems += elem
        underlying += elem
      }
    }

    def dequeue(): T = {
      val res = underlying.dequeue()
      elems -= res
      res
    }

    def headOption = underlying.headOption

    def isEmpty = underlying.isEmpty

    def toSeq = underlying.toSeq
  }

  // TODO: Improve naive representation of frontiers

  /** An element of the frontier of an operator */
  protected case class FrontierElem(coordinates: List[Int], elem: R, logProb: Double)
  protected val ordering = Ordering.by[FrontierElem, Double](_.logProb)
  /** The frontier of coordinates corresponding to an operator */
  protected type Frontier = DedupedPriorityQueue[FrontierElem]

  // The streams of elements corresponding to each nonterminal
  protected val streams: Map[NT, NonTerminalStream] =
    nts.map{ case (nt, _) => (nt, new NonTerminalStream(nt)) }

  // The operator streams per nonterminal
  protected val operators: Map[NT, Seq[OperatorStream]] =
    nts.map { case (nt, (_, prods)) =>
      nt -> prods.map(new OperatorStream(_))
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

    def populateNext() = {
      operators(nt).flatMap(_.getNext).sortBy(_._2).lastOption.map {
        case (r, d, op) =>
          buffer += ((r, d))
          //println(s"$nt: Adding ($r, $d)")
          op.advance()
          (r, d)
      }
    }

    @inline def get(i: Int): Option[(R, Double)] = {
      if (i > buffer.size) None
      else if (i < buffer.size) Some(buffer(i))
      else {
        populateNext()
      }
    }

    private var i = -1

    @inline def getNext(): Option[(R, Double)] = {
      i += 1
      get(i)
    }

  }

  /** Generates elements for a specific operator */
  protected class OperatorStream(val rule: ProductionRule[NT, R]) {
    private val frontier: Frontier = new Frontier(ordering) {
      def dominates(e1: FrontierElem, e2: FrontierElem) =
        e1.coordinates zip e2.coordinates forall ((_: Int) <= (_: Int)).tupled
    }
    private val arity = rule.arity
    private val typedStreams = rule.subTrees.map(streams)

    def init(): Unit = {
      typedStreams.mapM(_.get(0)) foreach { case ops =>
        val (operands, probs) = ops.unzip
        frontier += FrontierElem(
          List.fill(arity)(0),
          rule.builder(operands),
          probs.sum + rule.weight
        )
      }
    }
    init()

    @inline def getNext: Option[(R, Double, OperatorStream)] = {
      frontier.headOption.map(fe => (fe.elem, fe.logProb, this))
    }

    def advance(): Unit = {
      frontier.headOption.foreach { fe =>
        val newElems = fe.coordinates.zipWithIndex.map {
          case (elem, index) => fe.coordinates.updated(index, elem + 1)
        }
        val ops = newElems map (typedStreams.zip(_).mapM { case (stream, index) => stream.get(index) })
        frontier.dequeue()
        for {
          (optOperands, coords) <- ops.zip(newElems)
          ops <- optOperands
        } {
          //println(rule.outType + ": " + typedStreams.zip(coords).map{case (o,c) => o.nt.asInstanceOf[Label].getType.toString + s" -> $c"}.mkString(", "))
          val (operands, probs) = ops.unzip
          val elem = rule.builder(operands)
          val prob = probs.sum + rule.weight
          frontier += FrontierElem(coords, elem, prob)
        }
      }
    }

  }

  def getNext(nt: NT) = streams(nt).getNext()
  /*
  for ((nt, s) <- streams) {
    println(s"$nt -> ${s.buffer}")
  }

  for ((nt, ops) <- operators) {
    println(s"$nt")
    for (op <- ops) {
      println("  " + op.rule.outType)
      println("  " + op.frontier.toSeq.toList)
    }
  }
  */

  private def advance(): Unit = {
    val rules = nts.values.map(_._1).toSet
    val ops = operators.mapValues( _.find(rules contains _.rule).get)
    var toDo = ops.values.toSet
    def rec(op: OperatorStream): Unit = {
      if (toDo contains op) {
        op.rule.subTrees.map(ops).foreach(rec)
        op.advance()
        toDo -= op
      }
    }
    while (toDo.nonEmpty) rec(toDo.head)
  }
  advance()

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
      List("/home/manos/Documents/Leon/testcases/synthesis/userdefined/Grammar.scala")
    )
    val fd = program.definedFunctions.find(_.id.name == "min").get
    val sctx = new SynthesisContext(ctx, SynthesisSettings(), fd, program)
    val grammar = UserDefinedGrammar(sctx, program, Some(fd), fd.paramIds)
    val labels = List(BooleanType, IntegerType) map (Label(_, List()))//aspects.Tagged(Tags.Top, 0, None))))
    val bottomUp = new ProbwiseBottomupEnumerator(grammar, labels(1))
    grammar.printProductions(println)
    val horMap = (n: Int) => ProbwiseTopdownEnumerator.horizonMap(labels(n), grammar.getProductions)
    val topDown0 = ProbwiseTopdownEnumerator.iterator[Label, Expr](labels(0),
                                                                   grammar.getProductions,
                                                                   horMap(0).mapValues(_._2))
    val topDown1 = ProbwiseTopdownEnumerator.iterator[Label, Expr](labels(1),
                                                                   grammar.getProductions,
                                                                   horMap(1).mapValues(_._2))
    val before = System.currentTimeMillis()

    val b0 = for( _ <- 1 to 100) yield bottomUp.getNext(labels(0))
    val t0 = for( _ <- 1 to 100) yield topDown0.next

    b0 zip t0 foreach { case (b, t) =>
      println(f"${b.get._1}%60s: ${b.get._2}%3.3f vs ${t.expansion.produce}%60s: ${t.cost}%3.3f")
    }

    /*for (label <- labels; i <- 1 to 20; (e, prob) <- bottomUp.getNext(label) ) {
      //if (i%20000 == 0) println(f"$i: ${e.asString}%40s: $prob")
      println(f"${e.asString}%40s: $prob")
    }*/
    println(s"Time: ${System.currentTimeMillis() - before}")
  }
}
