import leon.lazyeval._
import leon.lazyeval.$._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._

/**
 * This is an version of the implicit recursive slowdwon queues of
 * Okasaki. Here, snoc (enqueue) and tail (dequeue) have constant
 * amortized time. But, accessing the ith element has linear time.
 * Achieving logarithmic time for ith element is independent of lazy
 * evaluation. We only need to change `Data` to a list instead of a single element,
 * and add invariants on exponential increase in the size of the Data relative to the
 * depth.
 */
object ImplicitQueue {

  // here Data is bascially a tree with elements stored only at the leaves
  sealed abstract class Data[T] {
    def size: BigInt = {
      this match {
        case Leaf(_)      => BigInt(1)
        case Node(l, r) => l.size + r.size
      }
    } ensuring (_ >= 1)
  }
  case class Node[T](l: Data[T], r: Data[T]) extends Data[T]
  case class Leaf[T](x: T) extends Data[T]

  sealed abstract class ZeroOne[T] {
    def level: BigInt = {
      this match {
        case Zero() => BigInt(0)
        case One(x) => x.size
      }
    }
  }
  case class Zero[T]() extends ZeroOne[T]
  case class One[T](d: Data[T]) extends ZeroOne[T]

  sealed abstract class OneTwo[T] {
    def level: BigInt = {
      this match {
        case OneF(x) => x.size
        case Two(x, y) => x.size
      }
    }

    // valid
    def valid: Boolean = {
      this match {
        case OneF(_) => true
        case Two(x, y) => x.size == y.size
      }
    }
  }
  case class OneF[T](d: Data[T]) extends OneTwo[T]
  case class Two[T](x: Data[T], y: Data[T]) extends OneTwo[T]

  sealed abstract class Queue[T] {
    def isEmpty: Boolean = {
      this match {
        case Shallow(Zero()) => true
        case _      => false
      }
    }

    def level: BigInt = {
      this match {
        case Shallow(d) => d.level
        case Deep(f, _, _) => f.level
      }
    }

    // queue invariant
    // level of mid is one greater than the level of this
    def valid: Boolean = {
      this match {
        case Shallow(_) => true
        case Deep(f, m, r) =>
          val mq = (m*)
          f.valid && (mq.level > this.level) && mq.valid
      }
    }

  }
  case class Shallow[T](e: ZeroOne[T]) extends Queue[T]
  case class Deep[T](f: OneTwo[T], m: $[Queue[T]], r: ZeroOne[T]) extends Queue[T]

  //def ssize[T](l: $[Stream[T]]): BigInt = (l*).size
  /*sealed abstract class DOption[T]
  case class DSome[T](d: Data[T]) extends DOption[T]
  case class DNone[T]() extends DOption[T]*/

  /*sealed abstract class QOption[T]
  case class QSome[T](q: Queue[T]) extends QOption[T]
  case class QNone[T]() extends QOption[T]*/

  def head[T](q: Queue[T]): Data[T] = {
    require(q.valid && !q.isEmpty)
    q match {
//      /case Shallow(Zero()) => DNone()
      case Shallow(One(x)) => x
      case Deep(Two(x, _), _, _) => x
      case Deep(OneF(x), _, _) => x
    }
  }

  def tail[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    val r: Queue[T] = (q match {
      case Shallow(One(x)) =>
        Shallow(Zero())
      case Deep(Two(x, y), m, r) =>
        Deep(OneF(y), m, r)
      case Deep(OneF(x), m, r) =>
        m.value match {
          case Shallow(Zero()) => // m is empty
            Shallow(r)
          case mq =>
            head(mq) match {
              case Node(x, y) =>
                Deep(Two(x, y), $(tail(mq)), r)
              //every other case is not allowed by the data structure invariants
            }
        }
    })
    r
  }
  // To ensure `res.valid` we need more preconditions. But, this is a correctness property

/*  def pot[T](q: Queue[T]): BigInt = {
    q match {
      case Deep(OneF(_), m, _) =>
        if(!m.isEvaluated) {

        }

      case _ => BigInt(0)
    }
  }*/

}
