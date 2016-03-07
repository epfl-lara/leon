/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

import scala.collection.SeqView
import scala.collection.mutable.ArrayBuffer

object SeqUtils {
  type Tuple[T] = Seq[T]

  def cartesianProduct[T](seqs: Tuple[Seq[T]]): Seq[Tuple[T]] = {
    val sizes = seqs.map(_.size)
    val max = sizes.product

    val result = new ArrayBuffer[Tuple[T]](max)
    var i = 0

    while (i < max) {
      var c = i
      var sel = -1
      val elem = for (s <- sizes) yield {
        val index = c % s
        c = c / s
        sel += 1
        seqs(sel)(index)
      }

      i+=1
      result += elem
    }

    result
  }

  def sumTo(sum: Int, arity: Int): Seq[Seq[Int]] = {
    require(arity >= 1)
    if (sum < arity) {
      Nil
    } else if (arity == 1) {
      Seq(Seq(sum))
    } else {
      (1 until sum).flatMap{ n => 
        sumTo(sum-n, arity-1).map( r => n +: r)
      }
    }
  }

  def sumToOrdered(sum: Int, arity: Int): Seq[Seq[Int]] = {
    def rec(sum: Int, arity: Int): Seq[Seq[Int]] = {
      require(arity > 0)
      if (sum < 0) Nil
      else if (arity == 1) Seq(Seq(sum))
      else for {
        n <- 0 to sum / arity
        rest <- rec(sum - arity * n, arity - 1)
      } yield n +: rest.map(n + _)
    }

    rec(sum, arity) filterNot (_.head == 0)
  }

  def groupWhile[T](es: Seq[T])(p: T => Boolean): Seq[Seq[T]] = {
    var res: Seq[Seq[T]] = Nil

    var c = es
    while (!c.isEmpty) {
      val (span, rest) = c.span(p)

      if (span.isEmpty) {
        res :+= Seq(rest.head)
        c = rest.tail
      } else {
        res :+= span
        c = rest
      }
    }

    res
  }
}

class CartesianView[+A](views: Seq[SeqView[A, Seq[A]]]) extends SeqView[Seq[A], Seq[Seq[A]]] {
  override protected def underlying: Seq[Seq[A]] = SeqUtils.cartesianProduct(views)

  override def length: Int = views.map{ _.size }.product

  override def apply(idx: Int): Seq[A] = {
    if (idx < 0 || idx >= length) throw new IndexOutOfBoundsException
    var c = idx
    for (v <- views) yield {
      val ic = c % v.size
      c /= v.size
      v(ic)
    }
  }

  override def iterator: Iterator[Seq[A]] = new Iterator[Seq[A]] {
    // It's unfortunate, but we have to use streams to memoize
    private val streams = views.map { _.toStream }
    private val current = streams.toArray

    // We take a note if there exists an empty view to begin with
    // (which means the whole iterator is empty)
    private val empty = streams exists { _.isEmpty }

    override def hasNext: Boolean = !empty && current.exists { _.nonEmpty }

    override def next(): Seq[A] = {
      if (!hasNext) throw new NoSuchElementException("next on empty iterator")
      // Propagate curry
      for (i <- (0 to streams.size).takeWhile(current(_).isEmpty)) {
        current(i) = streams(i)
      }

      val ret = current map { _.head }

      for (i <- (0 to streams.size)) {
        current(i) = current(i).tail
      }

      ret
    }
  }
}
