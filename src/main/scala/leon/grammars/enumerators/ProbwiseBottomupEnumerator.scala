package leon
package grammars
package enumerators

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class DedupedPriorityQueue[T]()(ord: Ordering[T]) extends mutable.PriorityQueue[T]()(ord) {
  val elems = new mutable.HashSet[T]()
  override def +=(elem: T) = {
    if (!(elems contains elem)) {
      elems += elem
      super.+=(elem)
    }
    this
  }

  override def dequeue(): T = {
    val res = super.dequeue()
    elems -= res
    res
  }
}

/**
  *
  * @tparam NT Nonterminal type
  * @tparam R Return type
  */
class ProbwiseBottomupEnumerator[NT, R] {

  /**
    *
    * @param coordinates
    * @param logProb
    * @param rule
    */
  case class FrontierElem(coordinates: List[Int], elem: R, logProb: Double)

  val ordering = Ordering.by[FrontierElem, Double](elem => elem.logProb)

  type Frontier = DedupedPriorityQueue[FrontierElem]

  class ProdStream(nt: NT, ops: List[OperatorProduction]) {
    val buffer: ArrayBuffer[(R, Double)] = new ArrayBuffer()

    def populateNext(): Unit = {
      ops.flatMap(_.get).sortBy(_._2).lastOption.foreach { case (r, d, op) =>
        buffer += ((r, d))
        op.advance()
      }
    }

    def get(i: Int) = buffer(i)
  }

  val streams: Map[NT, ProdStream] = Map()


  abstract class OperatorProduction(rule: ProductionRule[NT, R]) {
    val frontier: Frontier = new Frontier()(ordering)
    val arity = rule.subTrees.size
    val typedStreams = rule.subTrees.map(streams)
    frontier += FrontierElem(
      List.fill(arity)(0),
      rule.builder(typedStreams.map(_.get(0)._1)),
      typedStreams.map(_.get(0)._2).sum + Math.log(rule.weight)
    )
    def get: Option[(R, Double, OperatorProduction)] = {
      frontier.headOption.map(fe => (fe.elem, fe.logProb, this))
    }
    def advance(): Unit = {
      val fe = frontier.dequeue()
      val newElems = fe.coordinates.zipWithIndex.map{ case (elem, index) => fe.coordinates.updated(index, elem+1) }
      newElems foreach { coords =>
        val (operands, probs) = typedStreams.zip(coords).map { case (stream, index) =>
          stream.get(index)
        }.unzip
        val elem = rule.builder(operands)
        val prob = probs.sum + Math.log(rule.weight)
        frontier.enqueue(FrontierElem(coords, elem, prob))
      }
    }
  }



}
