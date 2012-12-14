package leon
package solvers.z3

import z3.scala._
import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

import scala.collection.mutable.{Set=>MutableSet,Map=>MutableMap}

case class Z3FunctionInvocation(funDef: FunDef, args: Seq[Z3AST])

// TODO: maybe a candidate for moving into purescala package?
class FunctionTemplate private(
  solver: AbstractZ3Solver,
  val funDef : FunDef,
  activatingBool : Identifier,
  condVars : Set[Identifier],
  exprVars : Set[Identifier],
  guardedExprs : Map[(Identifier,Boolean),Seq[Expr]]) {

  private val z3 = solver.z3

  private val asClauses : Seq[Expr] = {
    (for(((b,p),es) <- guardedExprs; e <- es) yield {
      Implies(if(!p) Not(Variable(b)) else Variable(b), e)
    }).toSeq
  }

  val z3ActivatingBool = solver.idToFreshZ3Id(activatingBool)

  private val z3FunDefArgs     = funDef.args.map( ad => solver.idToFreshZ3Id(ad.id))

  private val zippedCondVars   = condVars.map(id => (id, solver.idToFreshZ3Id(id)))
  private val zippedExprVars   = exprVars.map(id => (id, solver.idToFreshZ3Id(id)))
  private val zippedFunDefArgs = funDef.args.map(_.id) zip z3FunDefArgs

  val idToZ3Ids: Map[Identifier, Z3AST] = {
    Map(activatingBool -> z3ActivatingBool) ++
    zippedCondVars ++
    zippedExprVars ++
    zippedFunDefArgs
  }

  val asZ3Clauses: Seq[Z3AST] = asClauses.map(solver.toZ3Formula(_, idToZ3Ids).get)

  private val blockers : Map[(Identifier,Boolean),Set[FunctionInvocation]] = {
    val idCall = FunctionInvocation(funDef, funDef.args.map(_.toVariable))

    Map((for((p, es) <- guardedExprs) yield {
      val calls = es.foldLeft(Set.empty[FunctionInvocation])((s,e) => s ++ functionCallsOf(e)) - idCall
      if(calls.isEmpty) {
        None
      } else {
        Some((p, calls))
      }
    }).flatten.toSeq : _*)
  }

  val z3Blockers: Map[(Z3AST, Boolean), Set[Z3FunctionInvocation]] = blockers.map {
    case ((b, p), funs) => ((idToZ3Ids(b), p) -> funs.map(fi => Z3FunctionInvocation(fi.funDef, fi.args.map(solver.toZ3Formula(_, idToZ3Ids).get))))
  }

  def instantiate(aVar : Z3AST, aPol : Boolean, args : Seq[Z3AST]) : (Seq[Z3AST], Map[(Z3AST, Boolean), Set[Z3FunctionInvocation]]) = {
    assert(args.size == funDef.args.size)

    val idSubstMap : Map[Z3AST, Z3AST] =
      Map(z3ActivatingBool -> (if (aPol) aVar else z3.mkNot(aVar))) ++
      (zippedExprVars ++ zippedCondVars).map{ case (id, c) => c -> solver.idToFreshZ3Id(id) } ++
      (z3FunDefArgs zip args)

    val (from, to) = idSubstMap.unzip
    val (fromArray, toArray) = (from.toArray, to.toArray)

    val newClauses  = asZ3Clauses.map(z3.substitute(_, fromArray, toArray))
    val newBlockers = z3Blockers.map { case ((b, p), funs) =>
      val bp = if (b == z3ActivatingBool) {
        (aVar, p == aPol)
      } else {
        (idSubstMap(b), p)
      }

      val newFuns = funs.map(fi => fi.copy(args = fi.args.map(z3.substitute(_, fromArray, toArray))))

      bp -> newFuns
    }

    (newClauses, newBlockers)
  }

  override def toString : String = {
    "Template for def " + funDef.id + "(" + funDef.args.map(a => a.id + " : " + a.tpe).mkString(", ") + ") : " + funDef.returnType + " is :\n" +
    " * Activating boolean : " + activatingBool + "\n" + 
    " * Control booleans   : " + condVars.toSeq.map(_.toString).mkString(", ") + "\n" +
    " * Expression vars    : " + exprVars.toSeq.map(_.toString).mkString(", ") + "\n" +
    " * \"Clauses\"          : " + "\n    " + asClauses.mkString("\n    ") + "\n" +
    " * Block-map          : " + blockers.toString
  }
}

object FunctionTemplate {
  def mkTemplate(solver: AbstractZ3Solver, funDef: FunDef, isRealFunDef : Boolean = true) : FunctionTemplate = {
    val condVars : MutableSet[Identifier] = MutableSet.empty
    val exprVars : MutableSet[Identifier] = MutableSet.empty

    // represents clauses of the form:
    //    (~)id => expr && ... && expr
    val guardedExprs : MutableMap[(Identifier,Boolean),Seq[Expr]] = MutableMap.empty

    def storeGuarded(guardVar : Identifier, guardPol : Boolean, expr : Expr) : Unit = {
      assert(expr.getType == BooleanType)
      val p : (Identifier,Boolean) = (guardVar,guardPol)
      if(guardedExprs.isDefinedAt(p)) {
        val prev : Seq[Expr] = guardedExprs(p)
        guardedExprs(p) = expr +: prev
      } else {
        guardedExprs(p) = Seq(expr)
      }
    }

    def rec(pathVar : Identifier, pathPol : Boolean, expr : Expr) : Expr = {
      expr match {
        case l @ Let(i, e, b) =>
          val newExpr : Identifier = FreshIdentifier("lt", true).setType(i.getType)
          exprVars += newExpr
          val re = rec(pathVar, pathPol, e)
          storeGuarded(pathVar, pathPol, Equals(Variable(newExpr), re))
          val rb = rec(pathVar, pathPol, replace(Map(Variable(i) -> Variable(newExpr)), b))
          rb

        case m : MatchExpr => sys.error("MatchExpr's should have been eliminated.")

        case i @ IfExpr(cond, then, elze) => {
          if(!containsFunctionCalls(cond) && !containsFunctionCalls(then) && !containsFunctionCalls(elze)) {
            i
          } else {
            val newBool : Identifier = FreshIdentifier("b", true).setType(BooleanType)
            val newExpr : Identifier = FreshIdentifier("e", true).setType(i.getType)
            condVars += newBool
            exprVars += newExpr
            
            val crec = rec(pathVar, pathPol, cond)
            val trec = rec(newBool, true, then)
            val erec = rec(newBool, false, elze)

            storeGuarded(pathVar, pathPol, Iff(Variable(newBool), crec))
            storeGuarded(newBool, true,  Equals(Variable(newExpr), trec))
            storeGuarded(newBool, false, Equals(Variable(newExpr), erec))
            Variable(newExpr)
          }
        }

        case n @ NAryOperator(as, r) => r(as.map(a => rec(pathVar, pathPol, a))).setType(n.getType)
        case b @ BinaryOperator(a1, a2, r) => r(rec(pathVar, pathPol, a1), rec(pathVar, pathPol, a2)).setType(b.getType)
        case u @ UnaryOperator(a, r) => r(rec(pathVar, pathPol, a)).setType(u.getType)
        case t : Terminal => t
      }
    }

    // The precondition if it exists.
    val prec : Option[Expr] = funDef.precondition.map(p => matchToIfThenElse(p))

    val newBody : Option[Expr] = funDef.body.map(b => matchToIfThenElse(b))

    val invocation : Expr = FunctionInvocation(funDef, funDef.args.map(_.toVariable))

    val invocationEqualsBody : Option[Expr] = newBody match {
      case Some(body) if isRealFunDef =>
        val b : Expr = Equals(invocation, body)

        Some(if(prec.isDefined) {
          Implies(prec.get, b)
        } else {
          b
        })

      case _ =>
        None
    }

    val activatingBool : Identifier = FreshIdentifier("start", true).setType(BooleanType)

    if (isRealFunDef) {
      val finalPred : Option[Expr] = invocationEqualsBody.map(expr => rec(activatingBool, true, expr))
      finalPred.foreach(p => storeGuarded(activatingBool, true, p))
    } else {
       storeGuarded(activatingBool, false, BooleanLiteral(false))
       val newFormula = rec(activatingBool, true, newBody.get)
       storeGuarded(activatingBool, true, newFormula)
    }

    // Now the postcondition.
    if (funDef.hasPostcondition) {
      val post0 : Expr = matchToIfThenElse(funDef.getPostcondition)
      val post : Expr = replace(Map(ResultVariable() -> invocation), post0)

      val postHolds : Expr =
        if(funDef.hasPrecondition) {
          Implies(prec.get, post)
        } else {
          post
        }

      val finalPred2 : Expr = rec(activatingBool, true, postHolds)
      storeGuarded(activatingBool, true, postHolds)
    }

    new FunctionTemplate(solver, funDef, activatingBool, Set(condVars.toSeq : _*), Set(exprVars.toSeq : _*), Map(guardedExprs.toSeq : _*))
  }
}
