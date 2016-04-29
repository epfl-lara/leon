/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import solvers.z3._
import solvers._
import leon.invariant.templateSolvers.ExtendedUFSolver
import java.io._
import Util._
import PredicateUtil._
import evaluators._
import EvaluationResults._
import purescala.Extractors._

object SolverUtil {

  def modelToExpr(model: Model): Expr = {
    model.foldLeft(tru: Expr)((acc, elem) => {
      val (k, v) = elem
      val eq = Equals(k.toVariable, v)
      if (acc == tru) eq
      else And(acc, eq)
    })
  }

  def completeWithRefModel(currModel: Model, refModel: Model) = {
    new Model(refModel.toMap.map {
      case (id, _) if currModel.isDefinedAt(id) =>
        (id -> currModel(id))
      case (id, v) =>
        (id -> v)
    }.toMap)
  }

  def toZ3SMTLIB(expr: Expr, filename: String,
    theory: String, ctx: LeonContext, pgm: Program,
    useBitvectors: Boolean = false,
    bitvecSize: Int = 32) = {
    //create new solver, assert constraints and print
    val printSol = new ExtendedUFSolver(ctx, pgm)
    printSol.assertCnstr(expr)
    val writer = new PrintWriter(filename)
    writer.println(printSol.ctrsToString(theory))
    printSol.free()
    writer.flush()
    writer.close()
  }

  def verifyModel(e: Expr, model: Model, solver: SimpleSolverAPI) = {
    solver.solveSAT(And(e, modelToExpr(model))) match {
      case (Some(false), _) =>
        throw new IllegalStateException("Model doesn't staisfy formula!")
      case _ =>
    }
  }

  /**
   * A helper function that can be used to hardcode an invariant and see if it unsatifies the paths
   */
  def checkInvariant(expr: Expr, ctx: LeonContext, prog: Program): Option[Boolean] = {
    val idmap: Map[Expr, Expr] = variablesOf(expr).collect {
      case id @ _ if (id.name.toString == "a?") => id.toVariable -> InfiniteIntegerLiteral(6)
      case id @ _ if (id.name.toString == "c?") => id.toVariable -> InfiniteIntegerLiteral(2)
    }.toMap
    //println("found ids: " + idmap.keys)
    if (idmap.keys.nonEmpty) {
      val newpathcond = replace(idmap, expr)
      //check if this is solvable
      val solver = SimpleSolverAPI(SolverFactory("extendedUF", () => new ExtendedUFSolver(ctx, prog)))
      solver.solveSAT(newpathcond)._1 match {
        case Some(true) => {
          println("Path satisfiable for a?,c? -->6,2 ")
          Some(true)
        }
        case _ => {
          println("Path unsat for a?,c? --> 6,2")
          Some(false)
        }
      }
    } else None
  }

  def collectUNSATCores(ine: Expr, ctx: LeonContext, prog: Program): Expr = {
    var controlVars = Map[Variable, Expr]()
    var newEqs = Map[Expr, Expr]()
    val solver = new ExtendedUFSolver(ctx, prog)
    val newe = simplePostTransform {
      case e@(And(_) | Or(_)) => {
        val v = TVarFactory.createTempDefault("a", BooleanType).toVariable
        newEqs += (v -> e)
        val newe = Equals(v, e)

        //create new variable and add it in disjunction
        val cvar = FreshIdentifier("ctrl", BooleanType, true).toVariable
        controlVars += (cvar -> newe)
        solver.assertCnstr(Or(newe, cvar))
        v
      }
      case e => e
    }(ine)
    //create new variable and add it in disjunction
    val cvar = FreshIdentifier("ctrl", BooleanType, true).toVariable
    controlVars += (cvar -> newe)
    solver.assertCnstr(Or(newe, cvar))

    val res = solver.checkAssumptions(controlVars.keySet.map(Not.apply _))
    println("Result: " + res)
    val coreExprs = solver.getUnsatCore
    val simpcores = coreExprs.foldLeft(Seq[Expr]())((acc, coreExp) => {
      val Not(cvar @ Variable(_)) = coreExp
      val newexp = controlVars(cvar)
      //println("newexp: "+newexp)
      newexp match {
        // case Iff(v@Variable(_),rhs) if(newEqs.contains(v)) => acc
        case Equals(v @ Variable(_), rhs) if (v.getType == BooleanType && rhs.getType == BooleanType && newEqs.contains(v)) => acc
        case _ => {
          acc :+ newexp
        }
      }
    })
    val cores = Util.fix((e: Expr) => replace(newEqs, e))(createAnd(simpcores.toSeq))

    solver.free
    //cores
    ExpressionTransformer.unflatten(cores)
  }

  //tests if the solver uses nlsat
  def usesNLSat(solver: AbstractZ3Solver) = {
    //check for nlsat
    val x = FreshIdentifier("x", RealType).toVariable
    val testExpr = Equals(Times(x, x), FractionalLiteral(2, 1))
    solver.assertCnstr(testExpr)
    solver.check match {
      case Some(true) => true
      case _ => false
    }
  }

}
