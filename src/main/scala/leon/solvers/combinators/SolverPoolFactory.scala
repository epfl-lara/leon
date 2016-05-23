/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package combinators

import scala.collection.mutable.Queue
import scala.reflect.runtime.universe._

/**
 * This is a straitforward implementation of solver pools. The goal is to avoid
 * the cost of spawing processes for SMT solvers.
 *
 * Sadly smt-z3 is the only SMT solver that supports reset.
 *
 * If necessary, we may want to implement async reclaim/reset,
 * growing/shrinking pool size...
 */

class SolverPoolFactory[+S <: Solver](ctx: LeonContext, sf: SolverFactory[S]) extends SolverFactory[S] {

  val name = "Pool(" + sf.name + ")"

  var poolSize    = 0
  val poolMaxSize = 5

  private[this] val availables = Queue[S]()
  private[this] var inUse      = Set[Solver]()

  def getNewSolver(): S = {
    if (availables.isEmpty) {
      poolSize += 1
      availables += sf.getNewSolver()
    }

    val s = availables.dequeue()
    inUse += s
    s
  }

  override def reclaim(s: Solver) = {
    try {
      s.reset()
      inUse -= s
      s.reset()
      availables += s.asInstanceOf[S]
    } catch {
      case _: CantResetException =>
        inUse -= s
        s.free()
        sf.reclaim(s)
        availables += sf.getNewSolver()
    }
  }

  def init(): Unit = {
    for (i <- 1 to poolMaxSize) {
      availables += sf.getNewSolver()
    }

    poolSize = poolMaxSize
  }

  override def shutdown(): Unit = {
    for (s <- availables ++ inUse) {
      sf.reclaim(s)
    }

    availables.clear()

    inUse      = Set()
  }

  init()
}
