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

class UnrollingSolver(val context: LeonContext,
                      underlyings: SolverFactory[Solver],
                      maxUnrollings: Int = 3) extends Solver {

  private var theConstraint : Option[Expr] = None
  private var theModel : Option[Map[Identifier,Expr]] = None

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
    val simpleSolver = SimpleSolverAPI(underlyings)

    debugS("Check called on " + expr + "...")

    val template = getTemplate(expr)

    val aVar : Identifier = template.activatingBool
    var allClauses : Seq[Expr] = Nil
    var allBlockers : Map[Identifier,Set[FunctionInvocation]] = Map.empty

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
      var newBlockers : Map[Identifier,Set[FunctionInvocation]] = Map.empty

      for(blocker <- allBlockers.keySet; FunctionInvocation(funDef, args) <- allBlockers(blocker)) {
        val (nc, nb) = getTemplate(funDef).instantiate(blocker, args)
        newClauses = nc :: newClauses
        newBlockers = newBlockers ++ nb
      }

      allClauses = newClauses.flatten ++ allClauses
      allBlockers = newBlockers
    }

    val (nc, nb) = template.instantiate(aVar, template.funDef.args.map(a => Variable(a.id)))

    allClauses = nc.reverse
    allBlockers = nb

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
