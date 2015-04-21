package leon

import scala.reflect.runtime.universe._
import scala.concurrent.duration._

package object solvers {
  implicit class TimeoutableSolverFactory[+S <: TimeoutSolver : TypeTag](sf: SolverFactory[S]) {
    def withTimeout(to: Long) = {
      new TimeoutSolverFactory[S](sf, to)
    }

    def withTimeout(du: Duration) = {
      new TimeoutSolverFactory[S](sf, du.toMillis)
    }
  }
}
