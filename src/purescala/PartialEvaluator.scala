package purescala

import Common._
import Definitions._
import Trees._
import TypeTrees._

class PartialEvaluator(val program: Program) {
  val reporter = Settings.reporter

  def apply(expression:Expr) : Expr = expression
  // Simplifies by partially evaluating.
  // Of course, I still have to decide what 'simplified' means.
  def apply0(expression: Expr) : Expr = {
    def rec(expr: Expr, letMap: Map[Identifier,Expr]) : Expr = {
      println("****** rec called on " + expr + " *********")
      (expr match {
      case i @ IfExpr(cond, then, elze) => {
        val simpCond = rec(cond, letMap)
        if(simpCond == BooleanLiteral(true)) {
          rec(then, letMap)
        } else if(simpCond == BooleanLiteral(false)) {
          rec(elze, letMap)
        } else {
          IfExpr(simpCond, rec(then, letMap), rec(elze, letMap)).setType(i.getType)
        }
      }
      case CaseClassInstanceOf(cd, expr) if (expr.getType == CaseClassType(cd)) => BooleanLiteral(true)
      case CaseClassInstanceOf(cd, expr) if (!expr.getType.isInstanceOf[AbstractClassType] && expr.getType != CaseClassType(cd)) => BooleanLiteral(false)

      case CaseClass(cd, args) => CaseClass(cd, args.map(rec(_, letMap)))

      case ccs @ CaseClassSelector(cd1, CaseClass(cd2, args), sel) if cd1 == cd2 => {
        ccs
      }

      case FunctionInvocation(fd, args) if(fd.hasBody) => {
        val sargs = args.map(rec(_, letMap))
        if(sargs.forall(isGround(_))) {
          val subMap: Map[Expr,Expr] = Map((fd.args.map(_.toVariable) zip sargs) : _*)
          rec(replace(subMap, matchToIfThenElse(fd.body.get)), letMap) // WARNING ! WON'T TERMINATE IF FUNCTION LOOPS !!
        } else {
          FunctionInvocation(fd, sargs)
        }
      }
      case other => other
    })}

    rec(expression, Map.empty)
  }

  def isGround(expression: Expr) : Boolean = variablesOf(expression).isEmpty
}
