/* Copyright 2009-2014 EPFL, Lausanne */

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
        extends Solver with Interruptible with IncrementalSolver {

  private var constraints : List[Option[Expr]] = List(None)
  private var theModel : Option[Map[Identifier,Expr]] = None

  private var stop: Boolean = false

  def name = "Unr("+underlyings.name+")"

  def free {}

  def push() : Unit = {
    constraints = None :: constraints
  }

  def pop(lvl: Int) : Unit = {
    constraints = constraints.drop(lvl)
  }

  import context.reporter._

  def assertCnstr(expression : Expr) {
    if(!constraints.head.isEmpty) {
      fatalError("Multiple assertCnstr(...).")
    }
    constraints = Some(expression) :: constraints.tail
  }

  def check : Option[Boolean] = constraints.head.map { expr =>
    val solver = underlyings.getNewSolver//SimpleSolverAPI(underlyings)

    try {
      debugS("Check called on " + expr.asString + "...")

      val template = getTemplate(expr)

      val aVar : Identifier = template.activatingBool
      var allClauses : Seq[Expr] = Nil
      var allBlockers : Map[Identifier,Set[FunctionInvocation]] = Map.empty

      def unrollOneStep() : List[Expr] = {
        val blockersBefore = allBlockers

        var newClauses : List[Seq[Expr]] = Nil
        var newBlockers : Map[Identifier,Set[FunctionInvocation]] = Map.empty

        for(blocker <- allBlockers.keySet; FunctionInvocation(tfd, args) <- allBlockers(blocker)) {
          val (nc, nb) = getTemplate(tfd).instantiate(blocker, args)
          newClauses = nc :: newClauses
          newBlockers = newBlockers ++ nb
        }

        allClauses = newClauses.flatten ++ allClauses
        allBlockers = newBlockers
        newClauses.flatten
      }

      val (nc, nb) = template.instantiate(aVar, template.tfd.params.map(a => Variable(a.id)))

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
            solver.pop()
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
    } finally {
      solver.free
    }

  } getOrElse {
    Some(true)
  }

  def getModel : Map[Identifier,Expr] = {
    val vs : Set[Identifier] = constraints.head.map(variablesOf(_)).getOrElse(Set.empty)
    theModel.getOrElse(Map.empty).filter(p => vs(p._1))
  }

  override def interrupt(): Unit = {
    stop = true
  }

  override def recoverInterrupt(): Unit = {
    stop = false
  }

  private val tfdTemplateCache : MutableMap[TypedFunDef, FunctionTemplate] = MutableMap.empty
  private val exprTemplateCache : MutableMap[Expr, FunctionTemplate] = MutableMap.empty

  private def getTemplate(tfd: TypedFunDef): FunctionTemplate = {
    tfdTemplateCache.getOrElse(tfd, {
      val res = FunctionTemplate.mkTemplate(tfd, true)
      tfdTemplateCache += tfd -> res
      res
    })
  }

  private def getTemplate(body: Expr): FunctionTemplate = {
    exprTemplateCache.getOrElse(body, {
      val fakeFunDef = new FunDef(FreshIdentifier("fake", true), Nil, body.getType, variablesOf(body).toSeq.map(id => ValDef(id, id.getType)), DefType.MethodDef)
      fakeFunDef.body = Some(body)

      val res = FunctionTemplate.mkTemplate(fakeFunDef.typed, false)
      exprTemplateCache += body -> res
      res
    })
  }
}
