/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common._
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._
import purescala.Definitions._
import purescala.Constructors._

import evaluators._

class TemplateGenerator[T](val encoder: TemplateEncoder[T]) {
  private var cache     = Map[TypedFunDef, FunctionTemplate[T]]()
  private var cacheExpr = Map[Expr, FunctionTemplate[T]]()

  private val lambdaManager = new LambdaManager[T](encoder)

  def mkTemplate(body: Expr): FunctionTemplate[T] = {
    if (cacheExpr contains body) {
      return cacheExpr(body)
    }

    val fakeFunDef = new FunDef(FreshIdentifier("fake", alwaysShowUniqueID = true),
                                Nil,
                                body.getType,
                                variablesOf(body).toSeq.map(ValDef(_)),
                                DefType.MethodDef)

    fakeFunDef.body = Some(body)

    val res = mkTemplate(fakeFunDef.typed, false)
    cacheExpr += body -> res
    res
  }

  def mkTemplate(tfd: TypedFunDef, isRealFunDef: Boolean = true): FunctionTemplate[T] = {
    if (cache contains tfd) {
      return cache(tfd)
    }

    // The precondition if it exists.
    val prec : Option[Expr] = tfd.precondition.map(p => matchToIfThenElse(p))

    val newBody : Option[Expr] = tfd.body.map(b => matchToIfThenElse(b))
    val lambdaBody : Option[Expr] = newBody.map(b => simplifyHOFunctions(b))

    val invocation : Expr = FunctionInvocation(tfd, tfd.params.map(_.toVariable))

    val invocationEqualsBody : Option[Expr] = lambdaBody match {
      case Some(body) if isRealFunDef =>
        val b : Expr = appliedEquals(invocation, body)

        Some(if(prec.isDefined) {
          Implies(prec.get, b)
        } else {
          b
        })

      case _ =>
        None
    }

    val start : Identifier = FreshIdentifier("start", BooleanType, true)
    val pathVar : (Identifier, T) = start -> encoder.encodeId(start)

    val funDefArgs : Seq[Identifier] = tfd.params.map(_.id)
    val allArguments = funDefArgs ++ lambdaBody.map(lambdaArgs).toSeq.flatten
    val arguments : Seq[(Identifier, T)] = allArguments.map(id => id -> encoder.encodeId(id))

    val substMap : Map[Identifier, T] = arguments.toMap + pathVar

    val (bodyConds, bodyExprs, bodyGuarded, bodyLambdas) = if (isRealFunDef) {
      invocationEqualsBody.map(expr => mkClauses(start, expr, substMap)).getOrElse {
        (Map[Identifier,T](), Map[Identifier,T](), Map[Identifier,Seq[Expr]](), Map[T,LambdaTemplate[T]]())
      }
    } else {
      mkClauses(start, lambdaBody.get, substMap)
    }

    // Now the postcondition.
    val (condVars, exprVars, guardedExprs, lambdas) = tfd.postcondition match {
      case Some(post) =>
        val newPost : Expr = application(matchToIfThenElse(post), Seq(invocation))

        val postHolds : Expr =
          if(tfd.hasPrecondition) {
            Implies(prec.get, newPost)
          } else {
            newPost
          }

        val (postConds, postExprs, postGuarded, postLambdas) = mkClauses(start, postHolds, substMap)
        val allGuarded = (bodyGuarded.keys ++ postGuarded.keys).map { k => 
          k -> (bodyGuarded.getOrElse(k, Seq.empty) ++ postGuarded.getOrElse(k, Seq.empty))
        }.toMap

        (bodyConds ++ postConds, bodyExprs ++ postExprs, allGuarded, bodyLambdas ++ postLambdas)

      case None =>
        (bodyConds, bodyExprs, bodyGuarded, bodyLambdas)
    }

    val template = FunctionTemplate(tfd, encoder, lambdaManager,
      pathVar, arguments, condVars, exprVars, guardedExprs, lambdas, isRealFunDef)
    cache += tfd -> template
    template
  }

  private def lambdaArgs(expr: Expr): Seq[Identifier] = expr match {
    case Lambda(args, body) => args.map(_.id) ++ lambdaArgs(body)
    case _ => Seq.empty
  }

  private def appliedEquals(invocation: Expr, body: Expr): Expr = body match {
    case Lambda(args, lambdaBody) =>
      appliedEquals(application(invocation, args.map(_.toVariable)), lambdaBody)
    case _ => Equals(invocation, body)
  }

  def mkClauses(pathVar: Identifier, expr: Expr, substMap: Map[Identifier, T]):
               (Map[Identifier,T], Map[Identifier,T], Map[Identifier, Seq[Expr]], Map[T, LambdaTemplate[T]]) = {

    var condVars = Map[Identifier, T]()
    @inline def storeCond(id: Identifier) : Unit = condVars += id -> encoder.encodeId(id)
    @inline def encodedCond(id: Identifier) : T = substMap.getOrElse(id, condVars(id))

    var exprVars = Map[Identifier, T]()
    @inline def storeExpr(id: Identifier) : Unit = exprVars += id -> encoder.encodeId(id)

    // Represents clauses of the form:
    //    id => expr && ... && expr
    var guardedExprs = Map[Identifier, Seq[Expr]]()
    def storeGuarded(guardVar : Identifier, expr : Expr) : Unit = {
      assert(expr.getType == BooleanType)

      val prev = guardedExprs.getOrElse(guardVar, Nil)

      guardedExprs += guardVar -> (expr +: prev)
    }

    var lambdaVars = Map[Identifier, T]()
    @inline def storeLambda(id: Identifier) : T = {
      val idT = encoder.encodeId(id)
      lambdaVars += id -> idT
      idT
    }

    var lambdas = Map[T, LambdaTemplate[T]]()
    @inline def registerLambda(idT: T, lambda: LambdaTemplate[T]) : Unit = lambdas += idT -> lambda

    def requireDecomposition(e: Expr) = {
      exists{
        case (_: FunctionInvocation) | (_: Assert) | (_: Ensuring) | (_: Choose) | (_: Application) => true
        case _ => false
      }(e)
    }

    def rec(pathVar: Identifier, expr: Expr): Expr = {
      expr match {
        case a @ Assert(cond, _, body) =>
          storeGuarded(pathVar, rec(pathVar, cond))
          rec(pathVar, body)

        case e @ Ensuring(_, _) =>
          rec(pathVar, e.toAssert) 

        case l @ Let(i, e : Lambda, b) =>
          val re = rec(pathVar, e) // guaranteed variable!
          val rb = rec(pathVar, replace(Map(Variable(i) -> re), b))
          rb

        case l @ Let(i, e, b) =>
          val newExpr : Identifier = FreshIdentifier("lt", i.getType, true)
          storeExpr(newExpr)
          val re = rec(pathVar, e)
          storeGuarded(pathVar, Equals(Variable(newExpr), re))
          val rb = rec(pathVar, replace(Map(Variable(i) -> Variable(newExpr)), b))
          rb

        /* TODO: maybe we want this specialization?
        case l @ LetTuple(is, e, b) =>
          val tuple : Identifier = FreshIdentifier("t", TupleType(is.map(_.getType)), true)
          storeExpr(tuple)
          val re = rec(pathVar, e)
          storeGuarded(pathVar, Equals(Variable(tuple), re))

          val mapping = for ((id, i) <- is.zipWithIndex) yield {
            val newId = FreshIdentifier("ti", id.getType, true)
            storeExpr(newId)
            storeGuarded(pathVar, Equals(Variable(newId), TupleSelect(Variable(tuple), i+1)))

            (Variable(id) -> Variable(newId))
          }

          val rb = rec(pathVar, replace(mapping.toMap, b))
          rb
        */
        case m : MatchExpr => sys.error("'MatchExpr's should have been eliminated before generating templates.")
        case p : Passes    => sys.error("'Passes's should have been eliminated before generating templates.")
        case g : Gives     => sys.error("'Gives' should have been eliminated before generating templates.")

        case i @ Implies(lhs, rhs) =>
          implies(rec(pathVar, lhs), rec(pathVar, rhs))

        case a @ And(parts) =>
          andJoin(parts.map(rec(pathVar, _)))

        case o @ Or(parts) =>
          orJoin(parts.map(rec(pathVar, _)))

        case i @ IfExpr(cond, thenn, elze) => {
          if(!requireDecomposition(i)) {
            i
          } else {
            val newBool1 : Identifier = FreshIdentifier("b", BooleanType, true)
            val newBool2 : Identifier = FreshIdentifier("b", BooleanType, true)
            val newExpr : Identifier = FreshIdentifier("e", i.getType, true)

            storeCond(newBool1)
            storeCond(newBool2)

            storeExpr(newExpr)

            val crec = rec(pathVar, cond)
            val trec = rec(newBool1, thenn)
            val erec = rec(newBool2, elze)

            storeGuarded(pathVar, or(Variable(newBool1), Variable(newBool2)))
            storeGuarded(pathVar, or(not(Variable(newBool1)), not(Variable(newBool2))))
            // TODO can we improve this? i.e. make it more symmetrical?
            // Probably it's symmetrical enough to Z3.
            storeGuarded(pathVar, Equals(Variable(newBool1), crec))
            storeGuarded(newBool1, Equals(Variable(newExpr), trec))
            storeGuarded(newBool2, Equals(Variable(newExpr), erec))
            Variable(newExpr)
          }
        }

        case c @ Choose(cond, Some(impl)) =>
          rec(pathVar, impl)

        case c @ Choose(cond, None) =>
          val cid = FreshIdentifier("choose", c.getType, true)
          storeExpr(cid)
          storeGuarded(pathVar, application(cond, Seq(Variable(cid))))
          Variable(cid)

        case l @ Lambda(args, body) =>
          val idArgs : Seq[Identifier] = lambdaArgs(l)
          val trArgs : Seq[T] = idArgs.map(encoder.encodeId)

          val lid = FreshIdentifier("lambda", l.getType, true)
          val clause = appliedEquals(Variable(lid), l)

          val localSubst : Map[Identifier, T] = substMap ++ condVars ++ exprVars ++ lambdaVars
          val clauseSubst : Map[Identifier, T] = localSubst ++ (idArgs zip trArgs)
          val (lambdaConds, lambdaExprs, lambdaGuarded, lambdaTemplates) = mkClauses(pathVar, clause, clauseSubst)

          val ids: (Identifier, T) = lid -> storeLambda(lid)
          val dependencies: Map[Identifier, T] = variablesOf(l).map(id => id -> localSubst(id)).toMap
          val template = LambdaTemplate(ids, encoder, lambdaManager, pathVar -> encodedCond(pathVar), idArgs zip trArgs, lambdaConds, lambdaExprs, lambdaGuarded, lambdaTemplates, localSubst, dependencies, l)
          registerLambda(ids._2, template)

          Variable(lid)

        case n @ NAryOperator(as, r) => r(as.map(a => rec(pathVar, a)))
        case b @ BinaryOperator(a1, a2, r) => r(rec(pathVar, a1), rec(pathVar, a2))
        case u @ UnaryOperator(a, r) => r(rec(pathVar, a))
        case t : Terminal => t
      }
    }

    val p = rec(pathVar, expr)
    storeGuarded(pathVar, p)

    (condVars, exprVars, guardedExprs, lambdas)
  }

}
