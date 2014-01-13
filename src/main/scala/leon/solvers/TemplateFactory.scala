/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.HOTreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

import scala.collection.mutable.{Set=>MutableSet,Map=>MutableMap}

trait TemplateFactory[T] {

  def precondition: Expr

  def evaluator: Option[GroundEvaluator[T]]

  private val funDefTemplateCache : MutableMap[TypedFunDef, FunctionTemplate[T]] = MutableMap()
  private val exprTemplateCache   : MutableMap[Expr,        FunctionTemplate[T]] = MutableMap()

  private val closureIdToClosure : MutableMap[Identifier, (Expr, Map[Identifier,T])] = MutableMap()
  private val closureToClosureId : MutableMap[AnonymousFunction,         Identifier] = MutableMap()

  private val closureIdToEncoded : MutableMap[Identifier, T] = MutableMap()
  private val encodedToClosureId : MutableMap[T, Identifier] = MutableMap()

  private val encodedToId : MutableMap[T, Identifier] = MutableMap()

  def reset() {
    funDefTemplateCache.clear()
    exprTemplateCache.clear()

    closureIdToClosure.clear()
    closureToClosureId.clear()

    closureIdToEncoded.clear()
    encodedToClosureId.clear()

    encodedToId.clear()
  }

  def getTemplate(funDef: TypedFunDef) : FunctionTemplate[T] = funDefTemplateCache.getOrElse(funDef, {
    val res = TemplateFactory.mkTemplate(this, funDef, true)
    funDefTemplateCache += funDef -> res
    res
  })

  def getTemplate(body: Expr) : FunctionTemplate[T] = exprTemplateCache.getOrElse(body, {
    val args = variablesOf(body).toSeq.map(id => VarDecl(id, id.getType))
    val fakeFunDef = new FunDef(FreshIdentifier("fake", true), Seq(), body.getType, args)
    fakeFunDef.body = Some(body)

    val res = TemplateFactory.mkTemplate(this, TypedFunDef(fakeFunDef, isRealFunDef = false), false)
    exprTemplateCache += body -> res
    res
  })

  def decode(id: T): Identifier

  def replacer(idSubstMap: Map[T,T]): (T) => T

  protected def encode0(id: Identifier): T

  protected def translate0(from: Expr, subst: Map[Identifier, T]): T

  def encode(id: Identifier): T = closureIdToEncoded.get(id) match {
    case Some(encoded) => encoded
    case None => if (!id.getType.isInstanceOf[FunctionType]) encode0(id) else {
      val encoded = encode0(id)
      closureIdToEncoded(id) = encoded
      encodedToClosureId(encoded) = id
      encoded
    }
  }

  def translate(from: Expr, subst: Map[Identifier, T]): T = {
    val vars = variablesOf(from).map(id => id -> id.getType).toMap
    val closured = closureIdToEncoded.flatMap { case (id, ast) => if (vars.contains(id)) Some(id -> ast) else None }
    translate0(from, subst ++ closured)
  }

  def getClosure(t: T): Option[(Expr, Map[Identifier, T])] = encodedToClosureId.get(t) match {
    case Some(id) => Some(closureIdToClosure.get(id) match {
      case Some((from, map)) => (from, map)
      case None => (Variable(id), Map(id -> t))
    })
    case _ => None
  }

  private def uniqueClosure(af: AnonymousFunction, subst: Identifier => T): AnonymousFunction = {
    val vars = variablesOf(af).map(id => id -> {
      val encoded = closureIdToEncoded.getOrElse(id, subst(id))
      encodedToId.get(encoded) match {
        case Some(id) => id
        case None =>
          val freshID = id.freshen
          encodedToId(encoded) = freshID
          freshID
      }
    }).toMap

    replaceFromIDs(vars.mapValues(_.toVariable), af).asInstanceOf[AnonymousFunction]
  }

  def lambdaEquals(e1: Expr, e2: Expr, subst: Identifier => T): Boolean = e1 == e2 || ((e1, e2) match {
    case (af1 : AnonymousFunction, af2 : AnonymousFunction) => uniqueClosure(af1, subst) == uniqueClosure(af2, subst)
    case _ => false
  })

  def removeClosures(expr: Expr, subst: Identifier => T) = postMap({
    case af @ AnonymousFunction(args, body) =>
      val unique = uniqueClosure(af, subst)
      Some(closureToClosureId.get(unique) match {
        case Some(id) => Variable(id)
        case None =>
          val vars = variablesOf(af)
          val idToFresh = vars.map(id => id -> (if (id.getType.isInstanceOf[FunctionType]) id else id.freshen)).toMap
          val idToEncoded = vars.map(id => id -> closureIdToEncoded.getOrElse(id, subst(id))).toMap
          val anonymous = replaceFromIDs(idToFresh.mapValues(_.toVariable), af)
          val varMap = vars.map(id => idToFresh(id) -> idToEncoded(id)).toMap
          val id = FreshIdentifier("lambda", true).setType(af.getType)
          closureIdToClosure(id) = anonymous -> varMap
          closureToClosureId(unique) = id
          encode(id) // makes sure the mapping to Z3 is unified!
          Variable(id)
      })
    case _ => None
  })(expr)
}

object TemplateFactory {
  val splitAndOrImplies = false

  def mkClauses(pathVar: Identifier, expr: Expr) = {
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

              val ifExpr = partitions.map(Or(_)).reduceRight { (a: Expr, b: Expr) => IfExpr(a, BooleanLiteral(true), b) }

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

        case af @ AnonymousFunction(args, body) => af

        case n @ NAryOperator(as, r) => r(as.map(a => rec(pathVar, a)))
        case b @ BinaryOperator(a1, a2, r) => r(rec(pathVar, a1), rec(pathVar, a2))
        case u @ UnaryOperator(a, r) => r(rec(pathVar, a))
        case t : Terminal => t
      }
    }

    val newExpr = rec(pathVar, expr)
    storeGuarded(pathVar, newExpr)
    (Set(condVars.toSeq : _*), Set(exprVars.toSeq : _*), Map(guardedExprs.toSeq : _*))
  }

  private def prepareHOFunctionForTemplating(body: Expr) = {
    var resultToFunction : Map[Identifier, Expr] = Map()

    def computeResultType(tpe: TypeTree) : TypeTree = tpe match {
      case FunctionType(argTypes, returnType) => computeResultType(returnType)
      case _ => tpe
    }

    val resultType = computeResultType(body.getType)

    def replace(expr: Expr) = {
      val id = FreshIdentifier("__res__", true).setType(resultType)
      resultToFunction += (id -> expr)
      Variable(id)
    }

    def rec(expr: Expr): Expr = expr match {
      case IfExpr(cond, thenn, elze) => IfExpr(cond, rec(thenn), rec(elze))
      case fi @ FunctionInvocation(fd, args) => replace(fi)
      case af @ AnonymousFunction(args, body) => replace(af)
      case v @ Variable(id) => replace(v)
      case e => e
    }

    val newBody = rec(preProcess(body))
    (newBody, Map(resultToFunction.toSeq : _*))
  }

  def mkTemplate[T](factory: TemplateFactory[T], funDef: TypedFunDef, isRealFunDef : Boolean = true) : FunctionTemplate[T] = {
    // The precondition if it exists.
    val prec : Option[Expr] = funDef.precondition map preProcess map killForallExpressions

    val (newBody, resultMap) : (Option[Expr], Map[Identifier, Expr]) =
      if(funDef.body.isDefined && funDef.returnType.isInstanceOf[FunctionType]) {
        val (body, map) = prepareHOFunctionForTemplating(funDef.body.get)
        assert(map.forall(p => p._2.getType.isInstanceOf[FunctionType]))
        (Some(body), map)
      } else {
        (funDef.body map preProcess, Map())
      }

    val invocation = FunctionInvocation(funDef.fd, funDef.args.map(_.toVariable))
    val applicationArgs : Seq[Identifier] = buildApplicationArgs(funDef.returnType)

    val invocationEqualsBody : Option[Expr] = newBody match {
      case Some(body) if isRealFunDef =>
        val application = buildApplication(invocation, applicationArgs.map(_.toVariable))
        val b : Expr = Equals(application, body)

        Some(if(prec.isDefined) {
          Implies(prec.get, b)
        } else {
          b
        })

      case _ =>
        None
    }

    val activatingBool : Identifier = FreshIdentifier("start", true).setType(BooleanType)

    val (bodyConds, bodyExprs, bodyGuarded) : (Set[Identifier], Set[Identifier], Map[Identifier, Seq[Expr]]) =
      if (isRealFunDef) {
        invocationEqualsBody.map(mkClauses(activatingBool, _)).getOrElse(Set(), Set(), Map())
      } else {
        mkClauses(activatingBool, newBody.get)
      }

    // Now the postcondition.
    val (postConds, postExprs, postGuarded) : (Set[Identifier], Set[Identifier], Map[Identifier, Seq[Expr]]) =
      funDef.postcondition.filter(p => !p._1.getType.isInstanceOf[FunctionType]).map({ case (id, post0) =>
        val post : Expr = replace(Map(Variable(id) -> invocation), post0)

        val postHolds : Expr =
          if(funDef.hasPrecondition) {
            Implies(prec.get, post)
          } else {
            post
          }

        val cleanPost = expandLets(preProcess(postHolds))
        mkClauses(activatingBool, cleanPost)
      }).getOrElse(Set(), Set(), Map())

    val condVars = bodyConds ++ postConds
    val exprVars = bodyExprs ++ postExprs
    val guardedExprs = (bodyGuarded.keys ++ postGuarded.keys).map { key =>
      key -> (bodyGuarded.getOrElse(key, Seq()) ++ postGuarded.getOrElse(key, Seq()))
    }.toMap

    new FunctionTemplate(factory, funDef, activatingBool,
      condVars, exprVars, guardedExprs,
      resultMap, applicationArgs, isRealFunDef)
  }
}

