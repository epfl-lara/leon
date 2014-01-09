/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import scala.collection.mutable.{Map=>MutableMap}

class UnrollingSolver(val context   : LeonContext,
                      underlyings   : SolverFactory[Solver],
                      precondition  : Expr,
                      maxUnrollings : Int = 3) extends Solver {

  private var theConstraint : Option[Expr] = None
  private var theModel : Option[Map[Identifier,Expr]] = None

  def name = "Unr("+underlyings.name+")"

  def free {}

  import context.reporter._

  val templateFactory = new SimpleTemplateFactory(precondition)

  def assertCnstr(expression : Expr) {
    if(!theConstraint.isEmpty) {
      fatalError("Multiple assertCnstr(...).")
    }
    theConstraint = Some(expression)
  }

  def check : Option[Boolean] = theConstraint.map { expr =>
    val simpleSolver = SimpleSolverAPI(underlyings)

    debugS("Check called on " + expr + "...")

    val template = templateFactory.getTemplate(expr)

    val aVar : Identifier = template.activatingBool
    var allClauses : Seq[Expr] = Nil
    var allBlockers : Map[Identifier,Set[Invocation[Expr]]] = Map.empty

    def fullOpenExpr : Expr = {
      // And(Variable(aVar), And(allClauses.reverse))
      // Let's help the poor underlying guy a little bit...
      // Note that I keep aVar around, because it may negate one of the blockers, and we can't miss that!
      And(Variable(aVar), replace(Map(Variable(aVar) -> BooleanLiteral(true)), And(allClauses.reverse)))
    }

    def fullClosedExpr : Expr = {
      val blockedVars : Seq[Expr] = allBlockers.toSeq.map(p => Variable(p._1))

      And(
        replace(blockedVars.map(v => (v -> BooleanLiteral(false))).toMap, fullOpenExpr),
        And(blockedVars.map(Not(_)))
      )
    }

    def unrollOneStep() {
      val blockersBefore = allBlockers

      var newClauses : List[Seq[Expr]] = Nil
      var newBlockers : Map[Identifier,Set[Invocation[Expr]]] = Map.empty

      for(blocker <- allBlockers.keySet; Invocation(funDef, args) <- allBlockers(blocker)) {
        val (nc, nb) = templateFactory.getTemplate(funDef).instantiate(Variable(blocker), args)
        newBlockers = newBlockers ++ nb.map({ case (Variable(id), i) => id -> i })
        newClauses = nc :: newClauses
      }

      allClauses = newClauses.flatten ++ allClauses
      allBlockers = newBlockers
    }

    val (nc, nb) = template.instantiate(Variable(aVar), template.funDef.args.map(a => templateFactory.encode(a.id)))

    allClauses = nc.reverse
    allBlockers = nb.map({ case (Variable(id), i) => id -> i })

    var unrollingCount : Int = 0
    var done : Boolean = false
    var result : Option[Boolean] = None

    // We're now past the initial step.
    while(!done && unrollingCount < maxUnrollings) {
      debugS("At lvl : " + unrollingCount)
      val closed : Expr = fullClosedExpr

      debugS("Going for SAT with this:\n" + closed)

      simpleSolver.solveSAT(closed) match {
        case (Some(false), _) =>
          val open = fullOpenExpr
          debugS("Was UNSAT... Going for UNSAT with this:\n" + open)
          simpleSolver.solveSAT(open) match {
            case (Some(false), _) =>
              debugS("Was UNSAT... Done !")
              done = true
              result = Some(false)

            case _ =>
              debugS("Was SAT or UNKNOWN. Let's unroll !")
              unrollingCount += 1
              unrollOneStep()
          }

        case (Some(true), model) =>
          debugS("WAS SAT ! We're DONE !")
          done = true
          result = Some(true)
          theModel = Some(model)

        case (None, model) =>
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
}
