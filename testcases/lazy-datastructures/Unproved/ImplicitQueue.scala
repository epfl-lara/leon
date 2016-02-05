import leon.lazyeval._
import leon.lazyeval.$._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import scala.math.BigInt.int2bigInt

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

    def correct: Boolean = {
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

    // queue invariants
    // level of mid is one greater than the level of this
    def correct: Boolean = { // a property about the content
      this match {
        case Shallow(_) => true
        case Deep(f, m, r) =>
          val mq = (m*)
          f.correct && (mq.level > this.level) && mq.correct
      }
    }

    // a property about the state
    @invstate
    def valid: Boolean = {
      this match {
        case Shallow(_) => true
        case Deep(f, m, r) =>
          m.isEvaluated && (m*).valid
      }
    }

  }
  case class Shallow[T](e: ZeroOne[T]) extends Queue[T]
  case class Deep[T](f: OneTwo[T], m: $[Queue[T]], r: ZeroOne[T]) extends Queue[T]

  def head[T](q: Queue[T]): Data[T] = {
    require(q.correct && !q.isEmpty)
    q match {
//      /case Shallow(Zero()) => DNone()
      case Shallow(One(x)) => x
      case Deep(Two(x, _), _, _) => x
      case Deep(OneF(x), _, _) => x
    }
  }

  def tail[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.correct)
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

  /**
   * Properties of `valid`
   */
  def validMonotone[T](q: Queue[T], st1: Set[$[Queue[T]]], st2: Set[$[Queue[T]]]): Boolean = {
    require((q.valid withState st1) && st1.subsetOf(st2))
    // induction scheme
    (q match {
      case Shallow(_) => true
      case Deep(f, m, r) =>
       validMonotone(m*, st1, st2)
    }) &&
    //property
    (q.valid withState st2)
  } holds

}
