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

class TemplateGenerator[T](val encoder: TemplateEncoder[T],
                           val assumePreHolds: Boolean) {
  private var cache     = Map[TypedFunDef, FunctionTemplate[T]]()
  private var cacheExpr = Map[Expr, FunctionTemplate[T]]()

  val manager = new QuantificationManager[T](encoder)

  def mkTemplate(body: Expr): FunctionTemplate[T] = {
    if (cacheExpr contains body) {
      return cacheExpr(body)
    }

    val fakeFunDef = new FunDef(FreshIdentifier("fake", alwaysShowUniqueID = true),
                                Nil,
                                body.getType,
                                variablesOf(body).toSeq.map(ValDef(_)))

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

    val funDefArgs: Seq[Identifier] = tfd.params.map(_.id)
    val lambdaArguments: Seq[Identifier] = lambdaBody.map(lambdaArgs).toSeq.flatten
    val invocation : Expr = FunctionInvocation(tfd, funDefArgs.map(_.toVariable))

    val invocationEqualsBody : Option[Expr] = lambdaBody match {
      case Some(body) if isRealFunDef =>
        val b : Expr = And(Equals(invocation, body), liftedEquals(invocation, body, lambdaArguments))

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

    val allArguments : Seq[Identifier] = funDefArgs ++ lambdaArguments
    val arguments : Seq[(Identifier, T)] = allArguments.map(id => id -> encoder.encodeId(id))

    val substMap : Map[Identifier, T] = arguments.toMap + pathVar

    val (bodyConds, bodyExprs, bodyGuarded, bodyLambdas, bodyQuantifications) = if (isRealFunDef) {
      invocationEqualsBody.map(expr => mkClauses(start, expr, substMap)).getOrElse {
        (Map[Identifier,T](), Map[Identifier,T](), Map[Identifier,Seq[Expr]](), Map[T,LambdaTemplate[T]](), Seq[QuantificationTemplate[T]]())
      }
    } else {
      mkClauses(start, lambdaBody.get, substMap)
    }

    // Now the postcondition.
    val (condVars, exprVars, guardedExprs, lambdas, quantifications) = tfd.postcondition match {
      case Some(post) =>
        val newPost : Expr = application(matchToIfThenElse(post), Seq(invocation))

        val postHolds : Expr =
          if(tfd.hasPrecondition) {
            if (assumePreHolds) {
              And(prec.get, newPost)
            } else {
              Implies(prec.get, newPost)
            }
          } else {
            newPost
          }

        val (postConds, postExprs, postGuarded, postLambdas, postQuantifications) = mkClauses(start, postHolds, substMap)
        val allGuarded = (bodyGuarded.keys ++ postGuarded.keys).map { k => 
          k -> (bodyGuarded.getOrElse(k, Seq.empty) ++ postGuarded.getOrElse(k, Seq.empty))
        }.toMap

        (bodyConds ++ postConds, bodyExprs ++ postExprs, allGuarded, bodyLambdas ++ postLambdas, bodyQuantifications ++ postQuantifications)

      case None =>
        (bodyConds, bodyExprs, bodyGuarded, bodyLambdas, bodyQuantifications)
    }

    val template = FunctionTemplate(tfd, encoder, manager,
      pathVar, arguments, condVars, exprVars, guardedExprs, quantifications, lambdas, isRealFunDef)
    cache += tfd -> template
    template
  }

  private def lambdaArgs(expr: Expr): Seq[Identifier] = expr match {
    case Lambda(args, body) => args.map(_.id) ++ lambdaArgs(body)
    case IsTyped(_, _: FunctionType) => sys.error("Only applicable on lambda chains")
    case _ => Seq.empty
  }

  private def liftedEquals(invocation: Expr, body: Expr, args: Seq[Identifier], inlineFirst: Boolean = false): Expr = {
    def rec(i: Expr, b: Expr, args: Seq[Identifier], inline: Boolean): Seq[Expr] = i.getType match {
      case FunctionType(from, to) =>
        val (currArgs, nextArgs) = args.splitAt(from.size)
        val arguments = currArgs.map(_.toVariable)
        val apply = if (inline) application _ else Application
        val (appliedInv, appliedBody) = (apply(i, arguments), apply(b, arguments))
        Equals(appliedInv, appliedBody) +: rec(appliedInv, appliedBody, nextArgs, false)
      case _ =>
        assert(args.isEmpty, "liftedEquals should consume all provided arguments")
        Seq.empty
    }

    andJoin(rec(invocation, body, args, inlineFirst))
  }

  def mkClauses(pathVar: Identifier, expr: Expr, substMap: Map[Identifier, T]):
               (Map[Identifier,T], Map[Identifier,T], Map[Identifier, Seq[Expr]], Map[T, LambdaTemplate[T]], Seq[QuantificationTemplate[T]]) = {

    var condVars = Map[Identifier, T]()
    @inline def storeCond(id: Identifier) : Unit = condVars += id -> encoder.encodeId(id)
    @inline def encodedCond(id: Identifier) : T = substMap.getOrElse(id, condVars(id))

    var exprVars = Map[Identifier, T]()
    @inline def storeExpr(id: Identifier) : Unit = exprVars += id -> encoder.encodeId(id)

    // Represents clauses of the form:
    //    id => expr && ... && expr
    var guardedExprs = Map[Identifier, Seq[Expr]]()
    def storeGuarded(guardVar : Identifier, expr : Expr) : Unit = {
      assert(expr.getType == BooleanType, expr.asString(Program.empty)(LeonContext.empty))

      val prev = guardedExprs.getOrElse(guardVar, Nil)

      guardedExprs += guardVar -> (expr +: prev)
    }

    var lambdaVars = Map[Identifier, T]()
    @inline def storeLambda(id: Identifier) : T = {
      val idT = encoder.encodeId(id)
      lambdaVars += id -> idT
      idT
    }

    var quantifications = Seq[QuantificationTemplate[T]]()
    @inline def registerQuantification(quantification: QuantificationTemplate[T]): Unit =
      quantifications :+= quantification

    var lambdas = Map[T, LambdaTemplate[T]]()
    @inline def registerLambda(idT: T, lambda: LambdaTemplate[T]) : Unit = lambdas += idT -> lambda

    def requireDecomposition(e: Expr) = {
      exists{
        case (_: Choose) | (_: Forall) => true
        case (_: Assert) | (_: Ensuring) => true
        case (_: FunctionInvocation) | (_: Application) => true
        case _ => false
      }(e)
    }

    def rec(pathVar: Identifier, expr: Expr): Expr = {
      expr match {
        case a @ Assert(cond, err, body) =>
          rec(pathVar, IfExpr(cond, body, Error(body.getType, err getOrElse "assertion failed")))

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

        case c @ Choose(Lambda(params, cond)) =>

          val cs = params.map(_.id.freshen.toVariable)

          for (c <- cs) {
            storeExpr(c.id)
          }

          val freshMap = (params.map(_.id) zip cs).toMap

          storeGuarded(pathVar, replaceFromIDs(freshMap, cond))

          tupleWrap(cs)

        case l @ Lambda(args, body) =>
          val idArgs : Seq[Identifier] = lambdaArgs(l)
          val trArgs : Seq[T] = idArgs.map(id => substMap.getOrElse(id, encoder.encodeId(id)))

          val lid = FreshIdentifier("lambda", l.getType, true)
          val clause = liftedEquals(Variable(lid), l, idArgs, inlineFirst = true)

          val localSubst: Map[Identifier, T] = substMap ++ condVars ++ exprVars ++ lambdaVars
          val clauseSubst: Map[Identifier, T] = localSubst ++ (idArgs zip trArgs)
          val (lambdaConds, lambdaExprs, lambdaGuarded, lambdaTemplates, lambdaQuants) = mkClauses(pathVar, clause, clauseSubst)
          assert(lambdaQuants.isEmpty, "Unhandled quantification in lambdas in " + l)

          val ids: (Identifier, T) = lid -> storeLambda(lid)
          val dependencies: Map[Identifier, T] = variablesOf(l).map(id => id -> localSubst(id)).toMap
          val template = LambdaTemplate(ids, encoder, manager, pathVar -> encodedCond(pathVar),
            idArgs zip trArgs, lambdaConds, lambdaExprs, lambdaGuarded, lambdaTemplates, localSubst, dependencies, l)
          registerLambda(ids._2, template)

          Variable(lid)

        case f @ Forall(args, body) =>
          val TopLevelAnds(conjuncts) = body

          val conjunctQs = conjuncts.map { conjunct =>
            val vars = variablesOf(conjunct)
            val quantifiers = args.map(_.id).filter(vars).toSet

            val idQuantifiers : Seq[Identifier] = quantifiers.toSeq
            val trQuantifiers : Seq[T] = idQuantifiers.map(encoder.encodeId)

            val q: Identifier = FreshIdentifier("q", BooleanType, true)
            val q2: Identifier = FreshIdentifier("qo", BooleanType, true)
            val inst: Identifier = FreshIdentifier("inst", BooleanType, true)
            val guard: Identifier = FreshIdentifier("guard", BooleanType, true)

            val clause = Equals(Variable(inst), Implies(Variable(guard), conjunct))

            val qs: (Identifier, T) = q -> encoder.encodeId(q)
            val localSubst: Map[Identifier, T] = substMap ++ condVars ++ exprVars ++ lambdaVars
            val clauseSubst: Map[Identifier, T] = localSubst ++ (idQuantifiers zip trQuantifiers)
            val (qConds, qExprs, qGuarded, qTemplates, qQuants) = mkClauses(pathVar, clause, clauseSubst)
            assert(qQuants.isEmpty, "Unhandled nested quantification in "+clause)

            val binder = Equals(Variable(q), And(Variable(q2), Variable(inst)))
            val allQGuarded = qGuarded + (pathVar -> (binder +: qGuarded.getOrElse(pathVar, Seq.empty)))

            val template = QuantificationTemplate[T](encoder, manager, pathVar -> encodedCond(pathVar),
              qs, q2, inst, guard, idQuantifiers zip trQuantifiers, qConds, qExprs, allQGuarded, qTemplates, localSubst)
            registerQuantification(template)
            Variable(q)
          }

          andJoin(conjunctQs)

        case Operator(as, r) => r(as.map(a => rec(pathVar, a)))
      }
    }

    val p = rec(pathVar, expr)
    storeGuarded(pathVar, p)

    (condVars, exprVars, guardedExprs, lambdas, quantifications)
  }

}
