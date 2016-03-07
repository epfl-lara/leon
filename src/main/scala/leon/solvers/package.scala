/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import scala.reflect.runtime.universe._
import scala.concurrent.duration._

package object solvers {
  implicit class TimeoutableSolverFactory[+S <: TimeoutSolver : TypeTag](val sf: SolverFactory[S]) {
    def withTimeout(to: Long): TimeoutSolverFactory[S] = {
      sf match {
        case tsf: TimeoutSolverFactory[_] =>
          new TimeoutSolverFactory[S](tsf.sf, to)
        case _ =>
          new TimeoutSolverFactory[S](sf, to)
      }
    }

    def withTimeout(du: Duration): TimeoutSolverFactory[S] = {
      withTimeout(du.toMillis)
    }
  }
}
