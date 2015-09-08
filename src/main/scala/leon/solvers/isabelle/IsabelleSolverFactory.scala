package leon.solvers.isabelle

import scala.concurrent._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

import leon.LeonContext
import leon.purescala.Definitions._
import leon.solvers._

final class IsabelleSolverFactory(context: LeonContext, program: Program) extends SolverFactory[TimeoutSolver] {

  private val env = IsabelleEnvironment(context, program)

  override def shutdown() =
    Await.result(env.flatMap(_.system.dispose), Duration.Inf)

  def getNewSolver() =
    Await.result(env.map(_.solver), Duration.Inf)

}
