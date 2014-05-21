/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers.combinators

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

import evaluators._

import scala.collection.mutable.{Set=>MutableSet,Map=>MutableMap}

class FunctionTemplate private(
  val tfd : TypedFunDef,
  val activatingBool : Identifier,
  condVars : Set[Identifier],
  exprVars : Set[Identifier],
  guardedExprs : Map[Identifier,Seq[Expr]],
  isRealFunDef : Boolean) {

  private val funDefArgsIDs : Seq[Identifier] = tfd.params.map(_.id)

  private val asClauses : Seq[Expr] = {
    (for((b,es) <- guardedExprs; e <- es) yield {
      Implies(Variable(b), e)
    }).toSeq
  }

  val blockers : Map[Identifier,Set[FunctionInvocation]] = {
    val idCall = FunctionInvocation(tfd, tfd.params.map(_.toVariable))

    Map((for((b, es) <- guardedExprs) yield {
      val calls = es.foldLeft(Set.empty[FunctionInvocation])((s,e) => s ++ functionCallsOf(e)) - idCall
      if(calls.isEmpty) {
        None
      } else {
        Some((b, calls))
      }
    }).flatten.toSeq : _*)
  }

  private def idToFreshID(id : Identifier) : Identifier = {
    FreshIdentifier(id.name, true).setType(id.getType)
  }

  // We use a cache to create the same boolean variables.
  private val cache : MutableMap[Seq[Expr],Map[Identifier,Expr]] = MutableMap.empty 

  def instantiate(aVar : Identifier, args : Seq[Expr]) : (Seq[Expr], Map[Identifier,Set[FunctionInvocation]]) = {
    assert(args.size == tfd.params.size)

    val (wasHit,baseIDSubstMap) = cache.get(args) match {
      case Some(m) => (true,m)
      case None =>
        val newMap : Map[Identifier,Expr] = 
          (exprVars ++ condVars).map(id => id -> Variable(idToFreshID(id))).toMap ++
          (funDefArgsIDs zip args)
        cache(args) = newMap
        (false, newMap)
    }

    val idSubstMap : Map[Identifier,Expr] = baseIDSubstMap + (activatingBool -> Variable(aVar))
    val exprSubstMap : Map[Expr,Expr] = idSubstMap.map(p => (Variable(p._1), p._2))

    val newClauses  = asClauses.map(replace(exprSubstMap, _))

    val newBlockers = blockers.map { case (id, funs) =>
      val bp = if (id == activatingBool) {
        aVar
      } else {
        // That's not exactly safe...
        idSubstMap(id).asInstanceOf[Variable].id
      }

      val newFuns = funs.map(fi => fi.copy(args = fi.args.map(replace(exprSubstMap, _))))

      bp -> newFuns
    }

    (newClauses, newBlockers)
  }

  override def toString : String = {
    "Template for def " + tfd.id + "(" + tfd.params.map(a => a.id + " : " + a.tpe).mkString(", ") + ") : " + tfd.returnType + " is :\n" +
    " * Activating boolean : " + activatingBool + "\n" + 
    " * Control booleans   : " + condVars.toSeq.map(_.toString).mkString(", ") + "\n" +
    " * Expression vars    : " + exprVars.toSeq.map(_.toString).mkString(", ") + "\n" +
    " * \"Clauses\"          : " + "\n    " + asClauses.mkString("\n    ") + "\n" +
    " * Block-map          : " + blockers.toString
  }
}

object FunctionTemplate {
  def mkTemplate(tfd: TypedFunDef, isRealFunDef : Boolean = true) : FunctionTemplate = {
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

    def requireDecomposition(e: Expr) = {
      exists{
        case (_: FunctionInvocation) | (_: Assert) | (_: Ensuring) | (_: Choose) => true
        case _ => false
      }(e)
    }

    def rec(pathVar : Identifier, expr : Expr) : Expr = {
      expr match {
        case a @ Assert(cond, _, body) =>
          storeGuarded(pathVar, rec(pathVar, cond))
          rec(pathVar, body)

        case e @ Ensuring(body, id, post) =>
          rec(pathVar, Let(id, body, Assert(post, None, Variable(id))))

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
          Implies(rec(pathVar, lhs), rec(pathVar, rhs))

        case a @ And(parts) =>
          And(parts.map(rec(pathVar, _)))

        case o @ Or(parts) =>
          Or(parts.map(rec(pathVar, _)))

        case i @ IfExpr(cond, thenn, elze) => {
          if(!requireDecomposition(i)) {
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
    val prec : Option[Expr] = tfd.precondition.map(p => matchToIfThenElse(p))

    val newBody : Option[Expr] = tfd.body.map(b => matchToIfThenElse(b))

    val invocation : Expr = FunctionInvocation(tfd, tfd.params.map(_.toVariable))

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
    tfd.postcondition match {
      case Some((id, post)) =>
        val newPost : Expr = replace(Map(Variable(id) -> invocation), matchToIfThenElse(post))

        val postHolds : Expr =
          if(tfd.hasPrecondition) {
            Implies(prec.get, newPost)
          } else {
            newPost
          }

        val finalPred2 : Expr = rec(activatingBool,  postHolds)
        storeGuarded(activatingBool, finalPred2)
      case None =>

    }

    new FunctionTemplate(tfd, activatingBool, Set(condVars.toSeq : _*), Set(exprVars.toSeq : _*), Map(guardedExprs.toSeq : _*),
isRealFunDef)
  }
}
