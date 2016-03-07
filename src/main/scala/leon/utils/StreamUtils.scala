/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

object StreamUtils {

  /** Interleaves a stream of streams.
    * {{{
    * If streams = ((1,2,3),(4,5),(6,7,8,9),(10...),
    * Order taken    0 1     2
    * Order taken        3     4   5 6       7
    * Order taken                      8 9}}}
    * interleave(streams) = (1, 2, 4, 3, 5, 6, 7, 10, 8, 9...
    **/
  def interleave[T](streams: Stream[Stream[T]]): Stream[T] = {
    def rec(streams: Stream[Stream[T]], diag: Int): Stream[T] = {
      if(streams.isEmpty) Stream() else {
        val (take, leave) = streams.splitAt(diag)
        val (nonEmpty, empty) = take partition (_.nonEmpty)
        nonEmpty.map(_.head) #::: rec(nonEmpty.map(_.tail) ++ leave, diag + 1 - empty.size)
      }
    }
    rec(streams, 1)
  }

  /** Applies the interleaving to a finite sequence of streams. */
  def interleave[T](streams : Seq[Stream[T]]) : Stream[T] = {
    if (streams.isEmpty) Stream() else {
      val nonEmpty = streams filter (_.nonEmpty)
      nonEmpty.toStream.map(_.head) #::: interleave(nonEmpty.map(_.tail))
    }
  }

  private def cantorPair(x: Int, y: Int): Int = {
    ((x + y) * (x + y + 1)) / 2 + y
  }

  private def reverseCantorPair(z: Int): (Int, Int) = {
      val t = Math.floor((-1.0f + Math.sqrt(1.0f + 8.0f * z))/2.0f).toInt;
      val x = t * (t + 3) / 2 - z;
      val y = z - t * (t + 1) / 2;
      (x, y)
  }
  
  /** Combines two streams into one using cantor's unpairing function.
    *  Ensures that the stream terminates if both streams terminate */
  def cartesianProduct[A, B](sa: Stream[A], sb: Stream[B]): Stream[(A, B)] = {
    def combineRec[A, B](sa: Stream[A], sb: Stream[B])(i: Int): Stream[(A, B)] = {
      val (x, y) = reverseCantorPair(i)
      if(!sa.isDefinedAt(x) && !sb.isDefinedAt(y)) Stream.Empty
      else if(sa.isDefinedAt(x) && sb.isDefinedAt(y)) (sa(x), sb(y)) #:: combineRec(sa, sb)(i+1)
      else combineRec(sa, sb)(i+1)
    }
    combineRec(sa, sb)(0)
  }

  def cartesianProduct[T](streams : Seq[Stream[T]]) : Stream[List[T]] = {
    val dimensions = streams.size
    val vectorizedStreams = streams.map(new VectorizedStream(_))

    if(dimensions == 0)
      return Stream.cons(Nil, Stream.empty)

    if(streams.exists(_.isEmpty))
      return Stream.empty

    val indices = diagCount(dimensions)

    var allReached : Boolean = false
    val bounds : Array[Option[Int]] = for (s <- streams.toArray) yield {
      if (s.hasDefiniteSize) {
        Some(s.size)
      } else {
        None
      }
    }

    indices.takeWhile(_ => !allReached).flatMap { indexList =>
      var d = 0
      var continue = true
      var is = indexList
      var ss = vectorizedStreams.toList

      if ((indexList zip bounds).forall {
          case (i, Some(b)) => i >= b
          case _ => false
        }) {
        allReached = true
      }

      var tuple : List[T] = Nil

      while(continue && d < dimensions) {
        val i = is.head
        if(bounds(d).exists(i > _)) {
          continue = false
        } else try {
          // TODO can we speed up by caching the random access into
          // the stream in an indexedSeq? After all, `i` increases
          // slowly.
          tuple = ss.head(i) :: tuple
          is = is.tail
          ss = ss.tail
          d += 1
        } catch {
          case e : IndexOutOfBoundsException =>
            bounds(d) = Some(i - 1)
            continue = false
        }
      }
      if(continue) Some(tuple.reverse) else None
    }
  }

  private def diagCount(dim : Int) : Stream[List[Int]] = diag0(dim, 0)
  private def diag0(dim : Int, nextSum : Int) : Stream[List[Int]] = summingTo(nextSum, dim).append(diag0(dim, nextSum + 1))

  private def summingTo(sum : Int, n : Int) : Stream[List[Int]] = {
    // assert(sum >= 0)
    if(sum < 0) {
      Stream.empty
    } else if(n == 1) {
      Stream.cons(sum :: Nil, Stream.empty) 
    } else {
      (0 to sum).toStream.flatMap(fst => summingTo(sum - fst, n - 1).map(fst :: _))
    }
  }

  private class VectorizedStream[T](initial : Stream[T]) {
    private def mkException(i : Int) = new IndexOutOfBoundsException("Can't access VectorizedStream at : " + i)
    private def streamHeadIndex : Int = indexed.size
    private var stream  : Stream[T] = initial
    private var indexed : Vector[T] = Vector.empty

    def apply(index : Int) : T = {
      if(index < streamHeadIndex) {
        indexed(index)
      } else {
        val diff = index - streamHeadIndex // diff >= 0
        var i = 0
        while(i < diff) {
          if(stream.isEmpty) throw mkException(index)
          indexed = indexed :+ stream.head
          stream  = stream.tail
          i += 1
        }
        // The trick is *not* to read past the desired element. Leave it in the
        // stream, or it will force the *following* one...
        stream.headOption.getOrElse { throw mkException(index) }
      }
    }
  }
}
