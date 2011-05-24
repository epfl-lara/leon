package purescala

//TODO: what if we call halt before solve is started in every solvers
//TODO: stopping the FairZ3Solver seems to cause an error because model is not correct

import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

import Evaluator._

import scala.actors.Actor
import scala.actors.Actor._

import scala.concurrent.Lock

class ParallelSolver(reporter: Reporter, solvers: Solver*) extends Solver(reporter) {
  private val nbSolvers = solvers.size
  require(nbSolvers >= 2)

  override def setProgram(prog: Program): Unit = {
    solvers.foreach(_.setProgram(prog))
  }

  val description = "Solver running subsolvers in parallel"
  override val shortDescription = "parallel"

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

  def solve(expression: Expr) : Option[Boolean] = {
    foundSolution = false
    resultNotReady = true
    result = None
    nbResponses = 0

    solvers.foreach(s => new SolverRunner(s, expression).start())

    while(resultNotReady) {
      Thread.sleep(50) //TODO it does not seem to halt without the sleep...
    }
    result
  }

  def halt() {
    lock.acquire
    solvers.foreach(_.halt)
    lock.release
  }

}
