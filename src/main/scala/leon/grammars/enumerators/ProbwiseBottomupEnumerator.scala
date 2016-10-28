package leon
package grammars
package enumerators

import purescala.Expressions.Expr
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/** A priority queue which only allows unique elements.
  *
  * @param ord The ordering with which the elements will be held in the queue.
  */
class DedupedPriorityQueue[T](ord: Ordering[T]) {
  private val underlying = new mutable.PriorityQueue[T]()(ord)
  private val elems = new mutable.HashSet[T]()

  def +=(elem: T) = {
    if (!(elems contains elem)) {
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
}

/** An enumerator that jointly enumerates elements from a number of production rules by employing a bottom-up strategy.
  * After initialization, each nonterminal will produce a series of unique elements in decreasing probability order.
  *
  * @param nts A mapping from each nonterminal to the production rules corresponding to it.
  * @tparam NT Type of the nonterminal of the production rules.
  * @tparam R The type of enumerated elements.
  */
abstract class AbstractProbwiseBottomupEnumerator[NT, R](nts: Map[NT, Seq[ProductionRule[NT, R]]]) {

  // TODO: Optimize streams to not try to produce more values once they fail
  // TODO: Improve naive representation of frontiers

  /** An element of the frontier of an operator
    *
    * @param coordinates
    * @param elem
    * @param logProb
    */
  protected case class FrontierElem(coordinates: List[Int], elem: R, logProb: Double)
  protected val ordering = Ordering.by[FrontierElem, Double](_.logProb)
  /** The frontier of coordinates corresponding to an operator */
  protected type Frontier = DedupedPriorityQueue[FrontierElem]

  // The most probable terminal production for each nonterminal
  protected val firstTerminals = nts.mapValues {
    _.filter(_.arity == 0).sortBy(_.weight).lastOption
  }

  // The streams of elements corresponding to each nonterminal
  protected val streams: Map[NT, NonTerminalStream] =
    nts.map{ case (nt, _) => (nt, new NonTerminalStream(nt)) }

  // The operator streams per nonterminal
  protected val operators: Map[NT, Seq[OperatorStream]] =
    nts.map { case (nt, prods) =>
      nt -> (prods diff firstTerminals(nt).toSeq).map(new OperatorStream(_))
    }

  /** A class that represents the stream of generated elements for a specific nonterminal. */
  protected class NonTerminalStream(val nt: NT) {
    private val buffer: ArrayBuffer[(R, Double)] = new ArrayBuffer()

    // The first element to be produced will definitely be the terminal symbol with greatest probability.
    private def init(): Unit = {
      firstTerminals(nt).foreach { rule =>
        buffer += ( (rule.builder(Nil), (rule.weight)) )
        //println(s"$nt: Adding ${buffer(0)}")
      }
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
      if (buffer.isEmpty || i > buffer.size) None
      else if (i < buffer.size) Some(buffer(i))
      else {
        populateNext()
      }
    }

    private var i = -1

    def getNext(): Option[(R, Double)] = {
      i += 1
      get(i)
    }

  }

  /** Generates elements for a specific operator */
  protected class OperatorStream(rule: ProductionRule[NT, R]) {
    private val frontier: Frontier = new Frontier(ordering)
    private val arity = rule.arity
    private val typedStreams = rule.subTrees.map(streams)

    private def init(): Unit = {
      val optOps = typedStreams.map(_.get(0))
      if (optOps.forall(_.isDefined)) {
        val (operands, probs) = optOps.flatten.unzip
        frontier += FrontierElem(
          List.fill(arity)(0),
          rule.builder(operands),
          probs.sum + (rule.weight)
        )
      }
    }
    init()

    @inline def getNext: Option[(R, Double, OperatorStream)] = {
      frontier.headOption.map(fe => (fe.elem, fe.logProb, this))
    }

    def advance(): Unit = {
      if (!frontier.isEmpty) {
        val fe = frontier.dequeue()
        val newElems = fe.coordinates.zipWithIndex.map {
          case (elem, index) => fe.coordinates.updated(index, elem + 1)
        }
        newElems foreach { coords =>
          //println("Requesting " + typedStreams.zip(coords).map{case (o,c) => o.nt.toString + s" -> $c"}.mkString(", "))
          val optFromStreams = typedStreams.zip(coords).map { case (stream, index) =>
            // @mk: Lecture time: How do we know this will always work?
            // Notice how the advance() function can only advance each index by 1 at most.
            // Also, it is only called in NonTerminalStream AFTER it has added an
            // element to the buffer.
            // This means that the available indexed grow faster than the requested ones.
            stream.get(index)
          }
          if (optFromStreams.forall(_.isDefined)) {
            val (operands, probs) = optFromStreams.flatten.unzip
            val elem = rule.builder(operands)
            val prob = probs.sum + (rule.weight)
            frontier += FrontierElem(coords, elem, prob)
          }
        }
      }
    }
  }

  def getNext(nt: NT) = streams(nt).getNext()

}

class ProbwiseBottomupEnumerator(grammar: ExpressionGrammar, labels: Seq[Label])(implicit ctx: LeonContext)
  extends AbstractProbwiseBottomupEnumerator[Label, Expr](labels.map (l => l -> grammar.getProductions(l)).toMap)

object ProbwiseBottomupEnumerator {
  import leon.frontends.scalac.ExtractionPhase
  import leon.synthesis.{SynthesisSettings, SynthesisContext}
  import leon.utils.PreprocessingPhase
  import leon.purescala.Types._

  def main(args: Array[String]) = {
    val pipeline =  ExtractionPhase andThen
      new PreprocessingPhase
    val (ctx_, program) = pipeline.run(LeonContext.empty, List("/home/koukouto/Documents/Leon/testcases/synthesis/userdefined/Grammar.scala"))
    implicit val ctx = ctx_
    val fd = program.definedFunctions.find(_.id.name == "min").get
    val sctx = new SynthesisContext(ctx, new SynthesisSettings(), fd, program)
    val grammar = UserDefinedGrammar(sctx, program, Some(fd), fd.paramIds)
    val labels = List(BooleanType, IntegerType) map (Label(_, Nil))
    grammar.getProductions(labels(0))
    grammar.getProductions(labels(1))
    grammar.printProductions(println)
    val enum = new ProbwiseBottomupEnumerator(grammar, labels)
    val before = System.currentTimeMillis()
    for (label <- labels; i <- 1 to 1000000; (e, prob) <- enum.getNext(label) ) {
      //if (i%20000 == 0) println(f"$i: ${e.asString}%40s: $prob")
      println(f"${e.asString}%40s: $prob")
    }
    println(s"Time: ${System.currentTimeMillis() - before}")
  }
}