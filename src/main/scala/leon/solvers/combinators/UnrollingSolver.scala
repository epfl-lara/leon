/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import utils.Interruptible

import scala.collection.mutable.{Map=>MutableMap}

class UnrollingSolver(val context: LeonContext, underlyings: SolverFactory[IncrementalSolver]) 
        extends Solver with Interruptible {

  private var theConstraint : Option[Expr] = None
  private var theModel : Option[Map[Identifier,Expr]] = None

  private var stop: Boolean = false

  def name = "Unr("+underlyings.name+")"

  def free {}

  import context.reporter._

  def assertCnstr(expression : Expr) {
    if(!theConstraint.isEmpty) {
      fatalError("Multiple assertCnstr(...).")
    }
    theConstraint = Some(expression)
  }

  def check : Option[Boolean] = theConstraint.map { expr =>
    val solver = underlyings.getNewSolver//SimpleSolverAPI(underlyings)

    debugS("Check called on " + expr + "...")

    val template = getTemplate(expr)

    val aVar : Identifier = template.activatingBool
    var allClauses : Seq[Expr] = Nil
    var allBlockers : Map[Identifier,Set[FunctionInvocation]] = Map.empty

    def unrollOneStep() : List[Expr] = {
      val blockersBefore = allBlockers

      var newClauses : List[Seq[Expr]] = Nil
      var newBlockers : Map[Identifier,Set[FunctionInvocation]] = Map.empty

      for(blocker <- allBlockers.keySet; FunctionInvocation(funDef, args) <- allBlockers(blocker)) {
        val (nc, nb) = getTemplate(funDef).instantiate(blocker, args)
        newClauses = nc :: newClauses
        newBlockers = newBlockers ++ nb
      }

      allClauses = newClauses.flatten ++ allClauses
      allBlockers = newBlockers
      newClauses.flatten
    }

    val (nc, nb) = template.instantiate(aVar, template.funDef.args.map(a => Variable(a.id)))

    allClauses = nc.reverse
    allBlockers = nb

    var unrollingCount : Int = 0
    var done : Boolean = false
    var result : Option[Boolean] = None

    solver.assertCnstr(Variable(aVar))
    solver.assertCnstr(And(allClauses))
    // We're now past the initial step.
    while(!done && !stop) {
      debugS("At lvl : " + unrollingCount)

      solver.push()
      //val closed : Expr = fullClosedExpr
      solver.assertCnstr(And(allBlockers.keySet.toSeq.map(id => Not(id.toVariable))))

      debugS("Going for SAT with this:\n")

      solver.check match {

        case Some(false) =>
          solver.pop(1)
          //val open = fullOpenExpr
          debugS("Was UNSAT... Going for UNSAT with this:\n")
          solver.check match {
            case Some(false) =>
              debugS("Was UNSAT... Done !")
              done = true
              result = Some(false)

            case _ =>
              debugS("Was SAT or UNKNOWN. Let's unroll !")
              unrollingCount += 1
              val newClauses = unrollOneStep()
              solver.assertCnstr(And(newClauses))
          }

        case Some(true) =>
          val model = solver.getModel
          debugS("WAS SAT ! We're DONE !")
          done = true
          result = Some(true)
          theModel = Some(model)

        case None =>
          val model = solver.getModel
          debugS("WAS UNKNOWN ! We're DONE !")
          done = true
          result = Some(true)
          theModel = Some(model)
      }
    }
    result

  } getOrElse {
    Some(true)
  }

  def getModel : Map[Identifier,Expr] = {
    val vs : Set[Identifier] = theConstraint.map(variablesOf(_)).getOrElse(Set.empty)
    theModel.getOrElse(Map.empty).filter(p => vs(p._1))
  }

  override def interrupt(): Unit = {
    stop = true
  }

  override def recoverInterrupt(): Unit = {
    stop = false
  }

  private val funDefTemplateCache : MutableMap[FunDef, FunctionTemplate] = MutableMap.empty
  private val exprTemplateCache : MutableMap[Expr, FunctionTemplate] = MutableMap.empty

  private def getTemplate(funDef: FunDef): FunctionTemplate = {
    funDefTemplateCache.getOrElse(funDef, {
      val res = FunctionTemplate.mkTemplate(funDef, true)
      funDefTemplateCache += funDef -> res
      res
    })
  }

  private def getTemplate(body: Expr): FunctionTemplate = {
    exprTemplateCache.getOrElse(body, {
      val fakeFunDef = new FunDef(FreshIdentifier("fake", true), body.getType, variablesOf(body).toSeq.map(id => VarDecl(id, id.getType)))
      fakeFunDef.body = Some(body)

      val res = FunctionTemplate.mkTemplate(fakeFunDef, false)
      exprTemplateCache += body -> res
      res
    })
  }
}
