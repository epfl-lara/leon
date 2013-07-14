/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package datagen

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

import evaluators._

import scala.collection.mutable.{Map=>MutableMap}

/** Utility functions to generate values of a given type.
  * In fact, it could be used to generate *terms* of a given type,
  * e.g. by passing trees representing variables for the "bounds". */
class NaiveDataGen(ctx: LeonContext, p: Program, evaluator: Evaluator, _bounds : Option[Map[TypeTree,Seq[Expr]]] = None) extends DataGenerator {

  private val defaultBounds : Map[TypeTree,Seq[Expr]] = Map(
    Int32Type -> Seq(IntLiteral(0), IntLiteral(1), IntLiteral(-1))
  )

  val bounds = _bounds.getOrElse(defaultBounds)

  private val boolStream : Stream[Expr] =
    Stream.cons(BooleanLiteral(true), Stream.cons(BooleanLiteral(false), Stream.empty))

  class VectorizedStream[T](initial : Stream[T]) {
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

  private def intStream : Stream[Expr] = Stream.cons(IntLiteral(0), intStream0(1))
  private def intStream0(n : Int) : Stream[Expr] = Stream.cons(IntLiteral(n), intStream0(if(n > 0) -n else -(n-1)))

  def natStream : Stream[Expr] = natStream0(0)
  private def natStream0(n : Int) : Stream[Expr] = Stream.cons(IntLiteral(n), natStream0(n+1))

  private val streamCache : MutableMap[TypeTree,Stream[Expr]] = MutableMap.empty

  def generate(tpe : TypeTree, bounds : Map[TypeTree,Seq[Expr]] = defaultBounds) : Stream[Expr] = {
    streamCache.getOrElse(tpe, {
      val s = generate0(tpe, bounds)
      streamCache(tpe) = s
      s
    })
  }

  // TODO We should make sure the cache depends on the bounds (i.e. is not reused for different bounds.)
  private def generate0(tpe : TypeTree, bounds : Map[TypeTree,Seq[Expr]]) : Stream[Expr] = bounds.get(tpe).map(_.toStream).getOrElse {
    tpe match {
      case BooleanType =>
        boolStream

      case Int32Type =>
        intStream

      case TupleType(bses) =>
        naryProduct(bses.map(generate(_, bounds))).map(Tuple)

      case act : AbstractClassType =>
        // We prioritize base cases among the children.
        // Otherwise we run the risk of infinite recursion when
        // generating lists.
        val ccChildren = act.classDef.knownChildren.collect(_ match {
            case ccd : CaseClassDef => ccd
          }
        )
        val (leafs,conss) = ccChildren.partition(_.fields.size == 0)

        // The stream for leafs...
        val leafsStream = leafs.toStream.flatMap { ccd =>
          generate(classDefToClassType(ccd), bounds)
        }

        // ...to which we append the streams for constructors.
        leafsStream.append(interleave(conss.map { ccd =>
          generate(classDefToClassType(ccd), bounds)
        }))

      case cct : CaseClassType =>
        val ccd = cct.classDef
        if(ccd.fields.isEmpty) {
          Stream.cons(CaseClass(ccd, Nil), Stream.empty)
        } else {
          val fieldTypes = ccd.fields.map(_.tpe)
          val subStream = naryProduct(fieldTypes.map(generate(_, bounds)))
          subStream.map(prod => CaseClass(ccd, prod))
        }

      case _ => Stream.empty
    }
  }

  //def findModels(expr : Expr, maxModels : Int, maxTries : Int, bounds : Map[TypeTree,Seq[Expr]] = defaultBounds, forcedFreeVars: Option[Seq[Identifier]] = None) : Stream[Map[Identifier,Expr]] = {
  def generateFor(ins: Seq[Identifier], satisfying: Expr, maxValid : Int, maxEnumerated : Int) : Iterator[Seq[Expr]] = {
    evaluator.compile(satisfying, ins).map { evalFun =>
      val sat = EvaluationResults.Successful(BooleanLiteral(true))

      naryProduct(ins.map(id => generate(id.getType, bounds)))
        .take(maxEnumerated)
        .filter{s => evalFun(s) == sat }
        .take(maxValid)
        .iterator

    } getOrElse {
      Stream.empty.iterator
    }
  }

  // The following are stream utilities.

  // Takes a series of streams and merges them, round-robin style.
  private def interleave[T](streams : Seq[Stream[T]]) : Stream[T] = int0(streams)
  private def int0[T](streams : Seq[Stream[T]]) : Stream[T] = {
    var ss = streams
    while(!ss.isEmpty && ss.head.isEmpty) {
      ss = ss.tail
    }
    if(ss.isEmpty) return Stream.empty
    if(ss.size == 1) return ss(0)
    // TODO: This circular-shifts the list. I'd be interested in a constant time
    // operation. Perhaps simply by choosing the right data-structure?
    Stream.cons(ss.head.head, interleave(ss.tail :+ ss.head.tail))
  }

  // Takes a series of streams and enumerates their cartesian product.
  private def naryProduct[T](streams : Seq[Stream[T]]) : Stream[List[T]] = {
    val dimensions = streams.size
    val vectorizedStreams = streams.map(new VectorizedStream(_))

    if(dimensions == 0)
      return Stream.cons(Nil, Stream.empty)

    if(streams.exists(_.isEmpty))
      return Stream.empty

    val indices = if(streams.forall(_.hasDefiniteSize)) {
      val max = streams.map(_.size).max
      diagCount(dimensions).take(max)
    } else {
      diagCount(dimensions)
    }

    var allReached : Boolean = false
    val bounds : Array[Int] = Array.fill(dimensions)(Int.MaxValue)

    indices.takeWhile(_ => !allReached).flatMap { indexList =>
      var d = 0
      var continue = true
      var is = indexList
      var ss = vectorizedStreams.toList

      if(indexList.sum >= bounds.max) {
        allReached = true
      }

      var tuple : List[T] = Nil

      while(continue && d < dimensions) {
        var i = is.head
        if(i > bounds(d)) {
          continue = false
        } else try {
          // TODO can we speed up by caching the random access into
          // the stream in an indexedSeq? After all, `i` increases
          // slowly.
          tuple = (ss.head)(i) :: tuple
          is = is.tail
          ss = ss.tail
          d += 1
        } catch {
          case e : IndexOutOfBoundsException =>
            bounds(d) = i - 1
            continue = false
        }
      }
      if(continue) Some(tuple.reverse) else None
    }
  }

  // Utility function for n-way cartesian product.
  // Counts over indices in `dim` dimensions in a fair, diagonal, way.
  private def diagCount(dim : Int) : Stream[List[Int]] = diag0(dim, 0)
  private def diag0(dim : Int, nextSum : Int) : Stream[List[Int]] = summingTo(nextSum, dim).append(diag0(dim, nextSum + 1))
  // All tuples of dimension `n` whose sum is `sum`.
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
}
