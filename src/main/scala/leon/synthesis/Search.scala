/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import strategies._
import graph._

import scala.annotation.tailrec

import leon.utils.Interruptible
import java.util.concurrent.atomic.AtomicBoolean

class Search(val ctx: LeonContext, ci: SourceInfo, p: Problem, val strat: Strategy) extends Interruptible {
  val g = new Graph(p)

  val interrupted = new AtomicBoolean(false)

  strat.init(g.root)

  def doExpand(n: Node, sctx: SynthesisContext): Unit = {
    ctx.timers.synthesis.step.timed {
      n match {
        case an: AndNode =>
          ctx.timers.synthesis.applications.get(an.ri.asString(sctx)).timed {
            an.expand(new SearchContext(sctx, ci.source, an, this))
          }

        case on: OrNode =>
          on.expand(new SearchContext(sctx, ci.source, on, this))
      }
    }
  }

  @tailrec
  final def searchFrom(sctx: SynthesisContext, from: Node): Boolean = {
    strat.getNextToExpand(from) match {
      case Some(n) =>
        strat.beforeExpand(n)

        doExpand(n, sctx)

        strat.afterExpand(n)

        if (from.isSolved) {
          true
        } else if (interrupted.get) {
          false
        } else {
          searchFrom(sctx, from)
        }
      case None =>
        false
    }
  }

  def traversePathFrom(n: Node, path: List[Int]): Option[Node] = path match {
    case Nil =>
      Some(n)
    case x :: xs =>
      if (n.isExpanded && n.descendants.size > x) {
        traversePathFrom(n.descendants(x), xs)
      } else {
        None
      }
  }

  def traversePath(path: List[Int]): Option[Node] = {
    traversePathFrom(g.root, path)
  }

  def search(sctx: SynthesisContext): Stream[Solution] = {
    if (searchFrom(sctx, g.root)) {
      g.root.generateSolutions()
    } else {
      Stream.empty
    }
  }

  def interrupt(): Unit = {
    interrupted.set(true)
    strat.interrupt()
  }

  def recoverInterrupt(): Unit = {
    interrupted.set(false)
    strat.recoverInterrupt()
  }

  ctx.interruptManager.registerForInterrupts(this)
}
