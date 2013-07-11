/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers.z3

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

import evaluators._

import z3.scala._

import scala.collection.mutable.{Set=>MutableSet,Map=>MutableMap}

case class Z3FunctionInvocation(funDef: FunDef, args: Seq[Z3AST])

class FunctionTemplate private(
  solver: FairZ3Solver,
  val funDef : FunDef,
  activatingBool : Identifier,
  condVars : Set[Identifier],
  exprVars : Set[Identifier],
  guardedExprs : Map[Identifier,Seq[Expr]],
  isRealFunDef : Boolean) {

  private val isTerminatingForAllInputs : Boolean = (
       isRealFunDef
    && !funDef.hasPrecondition
    && solver.getTerminator.terminates(funDef).isGuaranteed
  )

  // if(isRealFunDef) {
  //   println("Just created template for %s... Safe? %s".format(funDef.id.name, isTerminatingForAllInputs.toString))
  // }

  private val z3 = solver.z3

  private val asClauses : Seq[Expr] = {
    (for((b,es) <- guardedExprs; e <- es) yield {
      Implies(Variable(b), e)
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

  val asZ3Clauses: Seq[Z3AST] = asClauses.map {
    solver.toZ3Formula(_, idToZ3Ids).getOrElse(sys.error("Could not translate to z3. Did you forget --xlang?"))
  }

  private val blockers : Map[Identifier,Set[FunctionInvocation]] = {
    val idCall = FunctionInvocation(funDef, funDef.args.map(_.toVariable))

    Map((for((b, es) <- guardedExprs) yield {
      val calls = es.foldLeft(Set.empty[FunctionInvocation])((s,e) => s ++ functionCallsOf(e)) - idCall
      if(calls.isEmpty) {
        None
      } else {
        Some((b, calls))
      }
    }).flatten.toSeq : _*)
  }

  val z3Blockers: Map[Z3AST,Set[Z3FunctionInvocation]] = blockers.map {
    case (b, funs) =>
      (idToZ3Ids(b) -> funs.map(fi => Z3FunctionInvocation(fi.funDef, fi.args.map(solver.toZ3Formula(_, idToZ3Ids).get))))
  }

  // We use a cache to create the same boolean variables.
  private val cache : MutableMap[Seq[Z3AST],Map[Z3AST,Z3AST]] = MutableMap.empty

  def instantiate(aVar : Z3AST, args : Seq[Z3AST]) : (Seq[Z3AST], Map[Z3AST,Set[Z3FunctionInvocation]]) = {
    assert(args.size == funDef.args.size)

    // The "isRealFunDef" part is to prevent evaluation of "fake"
    // function templates, as generated from FairZ3Solver.
    if(solver.evalGroundApps && isRealFunDef) {
      val ga = args.view.map(solver.asGround)
      if(ga.forall(_.isDefined)) {
        val leonArgs = ga.map(_.get).force
        val invocation = FunctionInvocation(funDef, leonArgs)
        solver.getEvaluator.eval(invocation) match {
          case EvaluationResults.Successful(result) =>
            val z3Invocation = z3.mkApp(solver.functionDefToDecl(funDef), args: _*)
            val z3Value      = solver.toZ3Formula(result).get
            val asZ3         = z3.mkEq(z3Invocation, z3Value)
            return (Seq(asZ3), Map.empty)

          case _ => throw new Exception("Evaluation of ground term should have succeeded.")
        }
      }
    }
    // ...end of ground evaluation part.

    val (wasHit,baseIDSubstMap) = cache.get(args) match {
      case Some(m) => (true,m)
      case None =>
        val newMap : Map[Z3AST,Z3AST] = 
          (zippedExprVars ++ zippedCondVars).map(p => p._2 -> solver.idToFreshZ3Id(p._1)).toMap ++
          (z3FunDefArgs zip args)
        cache(args) = newMap
        (false,newMap)
    }

    val idSubstMap : Map[Z3AST,Z3AST] = baseIDSubstMap + (z3ActivatingBool -> aVar)

    val (from, to) = idSubstMap.unzip
    val (fromArray, toArray) = (from.toArray, to.toArray)

    val newClauses  = asZ3Clauses.map(z3.substitute(_, fromArray, toArray))
    val newBlockers = z3Blockers.map { case (b, funs) =>
      val bp = if (b == z3ActivatingBool) {
        aVar
      } else {
        idSubstMap(b)
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
  val splitAndOrImplies = false

  def mkTemplate(solver: FairZ3Solver, funDef: FunDef, isRealFunDef : Boolean = true) : FunctionTemplate = {
    val condVars : MutableSet[Identifier] = MutableSet.empty
    val exprVars : MutableSet[Identifier] = MutableSet.empty

    // Represents clauses of the form:
    //    id => expr && ... && expr
    val guardedExprs : MutableMap[Identifier,Seq[Expr]] = MutableMap.empty

    def storeGuarded(guardVar : Identifier, expr : Expr) : Unit = {
      assert(expr.getType == BooleanType)
      if(guardedExprs.isDefinedAt(guardVar)) {
        val prev : Seq[Expr] = guardedExprs(guardVar)
        guardedExprs(guardVar) = expr +: prev
      } else {
        guardedExprs(guardVar) = Seq(expr)
      }
    }

    // Group elements that satisfy p toghether
    // List(a, a, a, b, c, a, a), with p = _ == a will produce:
    // List(List(a,a,a), List(b), List(c), List(a, a))
    def groupWhile[T](p: T => Boolean, l: Seq[T]): Seq[Seq[T]] = {
      var res: Seq[Seq[T]] = Nil

      var c = l

      while(!c.isEmpty) {
        val (span, rest) = c.span(p)

        if (span.isEmpty) {
          res = res :+ Seq(rest.head)
          c   = rest.tail
        } else {
          res = res :+ span
          c  = rest
        }
      }

      res
    }

    def rec(pathVar : Identifier, expr : Expr) : Expr = {
      expr match {
        case l @ Let(i, e, b) =>
          val newExpr : Identifier = FreshIdentifier("lt", true).setType(i.getType)
          exprVars += newExpr
          val re = rec(pathVar, e)
          storeGuarded(pathVar, Equals(Variable(newExpr), re))
          val rb = rec(pathVar, replace(Map(Variable(i) -> Variable(newExpr)), b))
          rb

        case l @ LetTuple(is, e, b) =>
          val tuple : Identifier = FreshIdentifier("t", true).setType(TupleType(is.map(_.getType)))
          exprVars += tuple
          val re = rec(pathVar, e)
          storeGuarded(pathVar, Equals(Variable(tuple), re))

          val mapping = for ((id, i) <- is.zipWithIndex) yield {
            val newId = FreshIdentifier("ti", true).setType(id.getType)
            exprVars += newId
            storeGuarded(pathVar, Equals(Variable(newId), TupleSelect(Variable(tuple), i+1)))

            (Variable(id) -> Variable(newId))
          }

          val rb = rec(pathVar, replace(mapping.toMap, b))
          rb

        case m : MatchExpr => sys.error("MatchExpr's should have been eliminated.")

        case i @ Implies(lhs, rhs) =>
          if (splitAndOrImplies) {
            if (containsFunctionCalls(i)) {
              rec(pathVar, IfExpr(lhs, rhs, BooleanLiteral(true)))
            } else {
              i
            }
          } else {
            Implies(rec(pathVar, lhs), rec(pathVar, rhs))
          }

        case a @ And(parts) =>
          if (splitAndOrImplies) {
            if (containsFunctionCalls(a)) {
              val partitions = groupWhile((e: Expr) => !containsFunctionCalls(e), parts)

              val ifExpr = partitions.map(And(_)).reduceRight{ (a: Expr, b: Expr) => IfExpr(a, b, BooleanLiteral(false)) }

              rec(pathVar, ifExpr)
            } else {
              a
            }
          } else {
            And(parts.map(rec(pathVar, _)))
          }

        case o @ Or(parts) =>
          if (splitAndOrImplies) {
            if (containsFunctionCalls(o)) {
              val partitions = groupWhile((e: Expr) => !containsFunctionCalls(e), parts)

              val ifExpr = partitions.map(Or(_)).reduceRight{ (a: Expr, b: Expr) => IfExpr(a, BooleanLiteral(true), b) }

              rec(pathVar, ifExpr)
            } else {
              o
            }
          } else {
            Or(parts.map(rec(pathVar, _)))
          }

        case i @ IfExpr(cond, thenn, elze) => {
          if(!containsFunctionCalls(cond) && !containsFunctionCalls(thenn) && !containsFunctionCalls(elze)) {
            i
          } else {
            val newBool1 : Identifier = FreshIdentifier("b", true).setType(BooleanType)
            val newBool2 : Identifier = FreshIdentifier("b", true).setType(BooleanType)
            val newExpr : Identifier = FreshIdentifier("e", true).setType(i.getType)

            condVars += newBool1
            condVars += newBool2

            exprVars += newExpr

            val crec = rec(pathVar, cond)
            val trec = rec(newBool1, thenn)
            val erec = rec(newBool2, elze)

            storeGuarded(pathVar, Or(Variable(newBool1), Variable(newBool2)))
            storeGuarded(pathVar, Or(Not(Variable(newBool1)), Not(Variable(newBool2))))
            // TODO can we improve this? i.e. make it more symmetrical?
            // Probably it's symmetrical enough to Z3.
            storeGuarded(pathVar, Iff(Variable(newBool1), crec)) 
            storeGuarded(newBool1, Equals(Variable(newExpr), trec))
            storeGuarded(newBool2, Equals(Variable(newExpr), erec))
            Variable(newExpr)
          }
        }

        case c @ Choose(ids, cond) =>
          val cid = FreshIdentifier("choose", true).setType(c.getType)
          exprVars += cid

          val m: Map[Expr, Expr] = if (ids.size == 1) {
            Map(Variable(ids.head) -> Variable(cid))
          } else {
            ids.zipWithIndex.map{ case (id, i) => Variable(id) -> TupleSelect(Variable(cid), i+1) }.toMap
          }

          storeGuarded(pathVar, replace(m, cond))
          Variable(cid)

        case n @ NAryOperator(as, r) => r(as.map(a => rec(pathVar, a))).setType(n.getType)
        case b @ BinaryOperator(a1, a2, r) => r(rec(pathVar, a1), rec(pathVar, a2)).setType(b.getType)
        case u @ UnaryOperator(a, r) => r(rec(pathVar, a)).setType(u.getType)
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
      val finalPred : Option[Expr] = invocationEqualsBody.map(expr => rec(activatingBool, expr))
      finalPred.foreach(p => storeGuarded(activatingBool, p))
    } else {
       val newFormula = rec(activatingBool, newBody.get)
       storeGuarded(activatingBool, newFormula)
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

      val finalPred2 : Expr = rec(activatingBool,  postHolds)
      storeGuarded(activatingBool, finalPred2)
    }

    new FunctionTemplate(solver, funDef, activatingBool, Set(condVars.toSeq : _*), Set(exprVars.toSeq : _*), Map(guardedExprs.toSeq : _*),
isRealFunDef)
  }
}
