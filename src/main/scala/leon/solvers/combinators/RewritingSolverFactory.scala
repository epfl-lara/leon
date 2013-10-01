/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

/** This is for solvers that operate by rewriting formulas into equisatisfiable ones.
  * They are essentially defined by two methods, one for preprocessing of the expressions,
  * and one for reconstructing the models. */
abstract class RewritingSolverFactory[S <: Solver,T](val sf : SolverFactory[S]) extends SolverFactory[Solver] {
  val context = sf.context
  val program = sf.program

  override def free() {
    sf.free()
  }

  override def recoverInterrupt() {
    sf.recoverInterrupt()
  }

  /** The type T is used to encode any meta information useful, for instance, to reconstruct
    * models. */
  def rewriteCnstr(expression : Expr) : (Expr,T)

  def reconstructModel(model : Map[Identifier,Expr], meta : T) : Map[Identifier,Expr]

  def getNewSolver() : Solver = {
    new Solver {
      val underlying : Solver = sf.getNewSolver()

      private def fail(because : String) : Nothing = {
        throw new Exception("Not supported in RewritingSolvers : " + because)
      }

      def push() : Unit = fail("push()")
      def pop(lvl : Int = 1) : Unit = fail("pop(lvl)")
      
      private var storedMeta : List[T] = Nil

      def assertCnstr(expression : Expr) {
        context.reporter.info("Asked to solve this in BAPA<:\n" + expression) 
        val (rewritten, meta) = rewriteCnstr(expression)
        storedMeta = meta :: storedMeta
        underlying.assertCnstr(rewritten)
      }

      def interrupt() {
        underlying.interrupt()
      }

      def recoverInterrupt() {
        underlying.recoverInterrupt()
      }

      def check : Option[Boolean] = {
        underlying.check
      }

      def checkAssumptions(assumptions : Set[Expr]) : Option[Boolean] = {
        fail("checkAssumptions(assumptions)")
      }

      def getModel : Map[Identifier,Expr] = {
        storedMeta match {
          case Nil => fail("reconstructing model without meta-information.")
          case m :: _ => reconstructModel(underlying.getModel, m)
        }
      }

      def getUnsatCore : Set[Expr] = {
        fail("getUnsatCore")
      }
    }
  }
}
