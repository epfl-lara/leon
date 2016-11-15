/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars
package enumerators

import leon.evaluators.DefaultEvaluator
import leon.purescala.Common.Identifier
import leon.purescala.Definitions.Program
import leon.synthesis.Example
import purescala.Expressions.Expr
import scala.collection.mutable.{ PriorityQueue, Set => MutableSet, HashMap, ArrayBuffer }

/** An enumerator that jointly enumerates elements from a number of production rules by employing a bottom-up strategy.
  * After initialization, each nonterminal will produce a series of unique elements in decreasing probability order.
  *
  * @param nts A mapping from each nonterminal to the production rules corresponding to it,
  *            and the rule which corresponds to the first element
  * @tparam NT Type of the nonterminal of the production rules.
  * @tparam R The type of enumerated elements.
  */
abstract class AbstractProbwiseBottomupEnumerator[NT, R](nts: Map[NT, (ProductionRule[NT, R], Seq[ProductionRule[NT, R]])]){
  protected type Rule = ProductionRule[NT, R]
  protected type Coords = Seq[Int]

  protected abstract class ProbTerm(rule: Rule, subs: Seq[StreamElem]){
    val r: R = rule.builder(subs map (_.r))
    val logProb: Double = subs.map(_.logProb).sum + rule.weight
  }
  protected type StreamElem <: ProbTerm
  protected def toElem(rule: Rule, subs: Seq[StreamElem]): StreamElem
  protected def isDistinct(elem: StreamElem, previous: Traversable[StreamElem]): Boolean

  // Represents the frontier of an operator, i.e. a set of the most probable combinations of operand indexes
  // such that each other combination that has not been generated yet has an index >= than one element of the frontier
  // Stores the elements in a priority queue by maximum probability
  class Frontier(dim: Int, rule: Rule, streams: Seq[NonTerminalStream]) {
    private val ordering = Ordering.by[FrontierElem, Double](_.streamElem.logProb)
    private val queue = new PriorityQueue[FrontierElem]()(ordering)
    private var futureElems = List.empty[ElemSuspension]

    private val byDim = Array.fill(dim)(
      HashMap[Int, MutableSet[FrontierElem]]()
        .withDefaultValue(MutableSet[FrontierElem]())
    )

    @inline private def dominates(e1: FrontierElem, e2: FrontierElem) =
      e1.coordinates zip e2.coordinates forall ((_: Int) <= (_: Int)).tupled

    @inline private def enqueue(elem: FrontierElem, grownDim: Int) = {
      val approved = grownDim < 0 || {
        val grownTo = elem.coordinates(grownDim)
        val elems = byDim(grownDim)(grownTo)
        !(elems exists (dominates(_, elem)))
      }
      if (approved) {
        queue += elem
        for (i <- 0 until dim) {
          val coord = elem.coordinates(i)
          byDim(i)(coord) += elem
        }
      }
    }

    // Add an element suspension to the frontier
    @inline def +=(l: ElemSuspension) = {
      futureElems ::= l
    }

    // Calculate an element from a suspension by retrieving elements from the respective nonterminal streams
    @inline private def elem(le: ElemSuspension): Option[(FrontierElem, Int)] = try {
      val children = le.coordinates.zip(streams).map { case (index, stream) => stream.get(index) }
      Some(FrontierElem(le.coordinates, toElem(rule, children)), le.grownIndex)
    } catch {
      case _: IndexOutOfBoundsException =>
        // Thrown by stream.get: A stream has been depleted
        None
    }

    // promote all elements suspensions to frontier elements
    private def promote() = {
      for {
        fe <- futureElems.reverse
        (elem, index) <- elem(fe)
      } enqueue(elem, index)
      futureElems = Nil
      // if (dim > 0) println(f"dim: $dim: 0: ${byDim(0)(0).map(_.coordinates(0)).max}%5d #: ${queue.size}%3d")
    }

    def dequeue() = {
      promote()
      val res = queue.dequeue()
      for (i <- 0 until dim)
        byDim(i)(res.coordinates(i)) -= res
      res
    }

    @inline def headOption = {
      promote()
      queue.headOption
    }

    @inline def isEmpty = queue.isEmpty && futureElems.isEmpty
  }

  /** A suspension of a frontier element (which has not yet retrieved its operands) */
  protected case class ElemSuspension(coordinates: List[Int], grownIndex: Int)

  /** An element of the frontier */
  protected case class FrontierElem(coordinates: List[Int], streamElem: StreamElem) {
    def nextElems = coordinates.zipWithIndex.map {
      case (elem, updated) => ElemSuspension(coordinates.updated(updated, elem + 1), updated)
    }
  }

  // The streams of elements corresponding to each nonterminal
  protected val streams: Map[NT, NonTerminalStream] =
    nts.map{ case (nt, _) => (nt, new NonTerminalStream(nt)) }

  // The operator streams per nonterminal
  protected val operators: Map[NT, Seq[OperatorStream]] =
    nts.map { case (nt, (advanced, prods)) =>
      nt -> prods.map(rule => new OperatorStream(rule, rule eq advanced))
    }

  /** A class that represents the stream of generated elements for a specific nonterminal. */
  protected class NonTerminalStream(nt: NT) extends Iterable[R] {

    protected val buffer: ArrayBuffer[StreamElem] = new ArrayBuffer()

    // The first element to be produced will be the one recursively computed by the horizon map.
    private def initialize(): Unit = {
      def rec(nt: NT): StreamElem = {
        val rule = nts(nt)._1
        toElem(rule, rule.subTrees.map(rec))
      }
      buffer += rec(nt)
    }

    initialize()

    private var lock = false

    // Add a new element to the buffer
    private def populateNext() = !lock && {
      try {
        lock = true
        var found = false
        while (!found) {
          //println(s"$nt: size is ${buffer.size}, populating")
          val (elem, op) = operators(nt).flatMap(_.getNext).maxBy(_._1.logProb)
          op.advance()
          if (isDistinct(elem, buffer)) {
            found = true
            buffer += elem
          }
          //println(s"$nt: Adding ($r, $d)")
        }
        lock = false
      } catch {
        case _: UnsupportedOperationException =>
          // maxBy was called on an empty list, i.e. all operators have been depleted
          // leave lock at true
      }
      !lock
    }

    // Get the i-th element of the buffer
    @inline def get(i: Int): StreamElem = {
      if (i == buffer.size) populateNext()
      buffer(i)
    }

    def iterator: Iterator[R] = new Iterator[R] {
      var i = 0
      def hasNext = i < buffer.size || i == buffer.size && populateNext()
      def next = {
        val res = get(i).r
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

    @inline def getNext: Option[(StreamElem, OperatorStream)] = {
      frontier.headOption.map(fe => (fe.streamElem, this))
    }

    // Remove the top element of the frontier and add its derivatives
    def advance(): Unit = if (!frontier.isEmpty) {
      frontier.dequeue().nextElems foreach { frontier += _ }
    }

    private def init(): Unit = {
      frontier += ElemSuspension(List.fill(arity)(0), -1)
      if (isAdvanced) advance()
    }
    init()
  }

  def iterator(nt: NT) = streams.get(nt).map(_.iterator).getOrElse(Iterator())
}

class ProbwiseBottomupEnumerator(protected val grammar: ExpressionGrammar, init: Label)(implicit ctx: LeonContext)
  extends AbstractProbwiseBottomupEnumerator[Label, Expr](ProbwiseBottomupEnumerator.productive(grammar, init))
  with GrammarEnumerator
{
  protected case class StreamElem(rule: Rule, subs: Seq[StreamElem]) extends ProbTerm(rule, subs)
  @inline protected def isDistinct(elem: StreamElem, previous: Traversable[StreamElem]): Boolean = true
  @inline protected def toElem(rule: Rule, subs: Seq[StreamElem]): StreamElem = {
    StreamElem(rule, subs)
  }
}


class EqClassesEnumerator(protected val grammar: ExpressionGrammar, init: Label, as: Seq[Identifier], examples: Seq[Example], program: Program)(implicit ctx: LeonContext)
  extends AbstractProbwiseBottomupEnumerator(ProbwiseBottomupEnumerator.productive(grammar, init))
  with GrammarEnumerator
{
  protected case class StreamElem(rule: Rule, subs: Seq[StreamElem]) extends ProbTerm(rule, subs) {

    lazy val sig: Option[Seq[Expr]] = {
      def evalEx(subs: Seq[Expr], ex: Example) = {
        evaluator.eval(rule.builder(subs), as.zip(ex.ins).toMap).result
      }
      if (subs.isEmpty) {
        examples.mapM(evalEx(Nil, _))
      } else {
        for {
          subSigs0 <- subs mapM (_.sig)
          subSigs = subSigs0.transpose
          res <- subSigs zip examples mapM (evalEx _).tupled
        } yield res
      }
    }

  }
  protected def isDistinct(elem: StreamElem, previous: Traversable[StreamElem]): Boolean = {
    elem.sig.isDefined &&
    (for {
      prev <- previous
      s1 <- prev.sig
      s2 <- elem.sig
    } yield (s1,s2)).forall{ case (s1, s2) => s1 != s2 }
  }

  protected lazy val evaluator = new DefaultEvaluator(ctx, program)

  @inline protected def toElem(rule: Rule, subs: Seq[StreamElem]): StreamElem = {
    StreamElem(rule, subs)
  }
}

object ProbwiseBottomupEnumerator {
  import GrammarEnumerator._
  def productive(grammar: ExpressionGrammar, init: Label)(implicit ctx: LeonContext) = {
    val ntMap = horizonMap(init, grammar.getProductions).collect {
      case (l, (Some(r), _)) => l -> (r, grammar.getProductions(l))
    }
    ntMap.map{ case (k, (r, prods)) => k -> (r, prods.filter(_.subTrees forall ntMap.contains)) }
  }
}
