package leon
package solvers

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

import Evaluator._

import scala.actors.Actor
import scala.actors.DaemonActor
import scala.actors.Actor._

import scala.concurrent.Lock

@deprecated("Unused, Untested, Unmaintained", "")
class ParallelSolver(solvers : Solver*) extends Solver(solvers(0).context) with NaiveIncrementalSolver {
  private val nbSolvers = solvers.size
  require(nbSolvers >= 2)

  private val reporter = context.reporter

  val description = "Solver running subsolvers in parallel " + solvers.map(_.description).mkString("(", ", ", ")")
  override val shortDescription = solvers.map(_.shortDescription).mkString("//")
  override val superseeds : Seq[String] = solvers.map(_.shortDescription).toSeq

  case class Solve(expr: Expr)
  case object Init
  case object Ready
  case class Result(res: Option[Boolean])

  private class SolverRunner(s: Solver) extends DaemonActor {

    /*
    val that = this
    val worker = new Actor {
      def act(): Unit = {
        while(true) {
          receive {
            case Solve(expr) => {
              reporter.info("Starting solver " + s.shortDescription)
              val res = s.solve(expr)
              that ! Result(res)
              reporter.info("Ending solver " + s.shortDescription)
            }
          }
        }
      }
    }
    */
    
    def act(): Unit = {
      while(true) {
        receive {
          case Init => {
            reporter.info("Init solver " + s.shortDescription)
            s.init 
            coordinator ! Ready
          }
          case Solve(expr) => {
            reporter.info("Starting solver " + s.shortDescription)
            val res = s.solve(expr)
            coordinator ! Result(res)
            reporter.info("Ending solver " + s.shortDescription)
          }
        }
      }
    }
  }

  private class Coordinator extends DaemonActor {

    def act(): Unit = {
      while(true) {
        receive {
          case s@Solve(expr) => {
            var nbResponses = 0

            solverRunners.foreach(_ ! Init)
            while(nbResponses < nbSolvers) {
              receive {
                case Ready => nbResponses += 1
              }
            }

            nbResponses = 0
            solverRunners.foreach(_ ! s)
            var result: Option[Boolean] = None

            while(nbResponses < nbSolvers) {
              receive {
                case Result(Some(b)) => {
                  solvers.foreach(_.halt)
                  result = Some(b)
                  nbResponses += 1
                }
                case Result(None) => {
                  nbResponses += 1
                }
              }
            }
            reply(result)
          }
        }
      }
    }
  }

  private val solverRunners = solvers.map(s => new SolverRunner(s).start())
  solverRunners.foreach(_.start())
  private val coordinator = new Coordinator
  coordinator.start()

  def solve(expression: Expr) : Option[Boolean] = {
    val result = (coordinator !? Solve(expression)).asInstanceOf[Option[Boolean]]
    result
  }

  override def halt() {
    solvers.foreach(_.halt)
  }

  override def setProgram(prog: Program): Unit = {
    solvers.foreach(_.setProgram(prog))
  }

}




/*
  private val lock = new Lock
  private var nbResponses: Int = 0
  private var result: Option[Boolean] = None
  private var resultNotReady: Boolean = true
  private var foundSolution: Boolean = false


  class SolverRunner(s: Solver, expr: Expr) extends Actor {
    def act() {
      reporter.info("Starting solver " + s.shortDescription)
      s.solve(expr) match {
        case Some(b) => {
          lock.acquire      
          nbResponses += 1
          if(!foundSolution) {
            solvers.foreach(_.halt)
            result = Some(b)
            foundSolution = true
          }
          lock.release
        }
        case None => {
          lock.acquire
          nbResponses += 1
          lock.release
        }
      }
      lock.acquire
      if(nbResponses >= nbSolvers)
        resultNotReady = false
      lock.release
      reporter.info("Ending solver " + s.shortDescription)
    }
  }
  */

