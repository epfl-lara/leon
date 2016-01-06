/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common._
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._
import purescala.TypeOps._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Quantification._

import Instantiation._

class TemplateGenerator[T](val encoder: TemplateEncoder[T],
                           val assumePreHolds: Boolean) {
  private var cache     = Map[TypedFunDef, FunctionTemplate[T]]()
  private var cacheExpr = Map[Expr, FunctionTemplate[T]]()

  private type Clauses = (
    Map[Identifier,T],
    Map[Identifier,T],
    Map[Identifier, Set[Identifier]],
    Map[Identifier, Seq[Expr]],
    Seq[LambdaTemplate[T]],
    Seq[QuantificationTemplate[T]]
  )

  private def emptyClauses: Clauses = (Map.empty, Map.empty, Map.empty, Map.empty, Seq.empty, Seq.empty)

  val manager = new QuantificationManager[T](encoder)

  def mkTemplate(body: Expr): FunctionTemplate[T] = {
    if (cacheExpr contains body) {
      return cacheExpr(body)
    }

    val fakeFunDef = new FunDef(FreshIdentifier("fake", alwaysShowUniqueID = true), Nil, variablesOf(body).toSeq.map(ValDef(_)), body.getType)

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

    val funDefArgs: Seq[Identifier] = tfd.paramIds
    val lambdaArguments: Seq[Identifier] = lambdaBody.map(lambdaArgs).toSeq.flatten
    val invocation : Expr = FunctionInvocation(tfd, funDefArgs.map(_.toVariable))

    val invocationEqualsBody : Option[Expr] = lambdaBody match {
      case Some(body) if isRealFunDef =>
        val b : Expr = And(
          liftedEquals(invocation, body, lambdaArguments),
          Equals(invocation, body))

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

    val (bodyConds, bodyExprs, bodyTree, bodyGuarded, bodyLambdas, bodyQuantifications) = if (isRealFunDef) {
      invocationEqualsBody.map(expr => mkClauses(start, expr, substMap)).getOrElse(emptyClauses)
    } else {
      mkClauses(start, lambdaBody.get, substMap)
    }

    // Now the postcondition.
    val (condVars, exprVars, condTree, guardedExprs, lambdas, quantifications) = tfd.postcondition match {
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

        val (postConds, postExprs, postTree, postGuarded, postLambdas, postQuantifications) = mkClauses(start, postHolds, substMap)
        (bodyConds ++ postConds, bodyExprs ++ postExprs, bodyTree merge postTree, bodyGuarded merge postGuarded, bodyLambdas ++ postLambdas, bodyQuantifications ++ postQuantifications)

      case None =>
        (bodyConds, bodyExprs, bodyTree, bodyGuarded, bodyLambdas, bodyQuantifications)
    }

    val template = FunctionTemplate(tfd, encoder, manager,
      pathVar, arguments, condVars, exprVars, condTree, guardedExprs, quantifications, lambdas, isRealFunDef)
    cache += tfd -> template
    template
  }

  private def lambdaArgs(expr: Expr): Seq[Identifier] = expr match {
    case Lambda(args, body) => args.map(_.id.freshen) ++ lambdaArgs(body)
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
        rec(appliedInv, appliedBody, nextArgs, false) :+ Equals(appliedInv, appliedBody)
      case _ =>
        assert(args.isEmpty, "liftedEquals should consume all provided arguments")
        Seq.empty
    }

    andJoin(rec(invocation, body, args, inlineFirst))
  }

  private def minimalFlattening(inits: Set[Identifier], conj: Expr): (Set[Identifier], Expr) = {
    var mapping: Map[Expr, Expr] = Map.empty
    var quantified: Set[Identifier] = inits
    var quantifierEqualities: Seq[(Expr, Identifier)] = Seq.empty

    val newConj = postMap {
      case expr if mapping.isDefinedAt(expr) =>
        Some(mapping(expr))

      case expr @ QuantificationMatcher(c, args) =>
        val isMatcher = args.exists { case Variable(id) => quantified(id) case _ => false }
        val isRelevant = (variablesOf(expr) & quantified).nonEmpty
        if (!isMatcher && isRelevant) {
          val newArgs = args.map {
            case arg @ QuantificationMatcher(_, _) if (variablesOf(arg) & quantified).nonEmpty =>
              val id = FreshIdentifier("flat", arg.getType)
              quantifierEqualities :+= (arg -> id)
              quantified += id
              Variable(id)
            case arg => arg
          }

          val newExpr = replace((args zip newArgs).toMap, expr)
          mapping += expr -> newExpr
          Some(newExpr)
        } else {
          None
        }

      case _ => None
    } (conj)

    val flatConj = implies(andJoin(quantifierEqualities.map {
      case (arg, id) => Equals(arg, Variable(id))
    }), newConj)

    (quantified, flatConj)
  }

  def mkClauses(pathVar: Identifier, expr: Expr, substMap: Map[Identifier, T]): Clauses = {
    val (p, (condVars, exprVars, condTree, guardedExprs, lambdas, quantifications)) = mkExprClauses(pathVar, expr, substMap)
    val allGuarded = guardedExprs + (pathVar -> (p +: guardedExprs.getOrElse(pathVar, Seq.empty)))
    (condVars, exprVars, condTree, allGuarded, lambdas, quantifications)
  }

  private def mkExprClauses(pathVar: Identifier, expr: Expr, substMap: Map[Identifier, T]): (Expr, Clauses) = {

    var condVars = Map[Identifier, T]()
    var condTree = Map[Identifier, Set[Identifier]](pathVar -> Set.empty).withDefaultValue(Set.empty)
    def storeCond(pathVar: Identifier, id: Identifier) : Unit = {
      condVars += id -> encoder.encodeId(id)
      condTree += pathVar -> (condTree(pathVar) + id)
    }

    @inline def encodedCond(id: Identifier) : T = substMap.getOrElse(id, condVars(id))

    var exprVars = Map[Identifier, T]()
    @inline def storeExpr(id: Identifier) : Unit = exprVars += id -> encoder.encodeId(id)

    // Represents clauses of the form:
    //    id => expr && ... && expr
    var guardedExprs = Map[Identifier, Seq[Expr]]()
    def storeGuarded(guardVar : Identifier, expr : Expr) : Unit = {
      assert(expr.getType == BooleanType, expr.asString(Program.empty)(LeonContext.empty) + " is not of type Boolean")

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

    var lambdas = Seq[LambdaTemplate[T]]()
    @inline def registerLambda(lambda: LambdaTemplate[T]) : Unit = lambdas :+= lambda

    def requireDecomposition(e: Expr) = {
      exists{
        case (_: Choose) | (_: Forall) | (_: Lambda) => true
        case (_: Assert) | (_: Ensuring) => true
        case (_: FunctionInvocation) | (_: Application) => true
        case _ => false
      }(e)
    }

    def groupWhile[T](es: Seq[T])(p: T => Boolean): Seq[Seq[T]] = {
      var res: Seq[Seq[T]] = Nil

      var c = es
      while (!c.isEmpty) {
        val (span, rest) = c.span(p)

        if (span.isEmpty) {
          res :+= Seq(rest.head)
          c = rest.tail
        } else {
          res :+= span
          c = rest
        }
      }

      res
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
          if (requireDecomposition(i)) {
            rec(pathVar, Or(Not(lhs), rhs))
          } else {
            implies(rec(pathVar, lhs), rec(pathVar, rhs))
          }

        case a @ And(parts) =>
          val partitions = groupWhile(parts)(!requireDecomposition(_))
          partitions.map(andJoin) match {
            case Seq(e) => e
            case seq =>
              val newExpr : Identifier = FreshIdentifier("e", BooleanType, true)
              storeExpr(newExpr)

              def recAnd(pathVar: Identifier, partitions: Seq[Expr]): Unit = partitions match {
                case x :: Nil if !requireDecomposition(x) =>
                  storeGuarded(pathVar, Equals(Variable(newExpr), x))

                case x :: xs =>
                  val newBool : Identifier = FreshIdentifier("b", BooleanType, true)
                  storeCond(pathVar, newBool)

                  val xrec = rec(pathVar, x)
                  storeGuarded(pathVar, Equals(Variable(newBool), xrec))
                  storeGuarded(pathVar, Implies(Not(Variable(newBool)), Not(Variable(newExpr))))

                  recAnd(newBool, xs)

                case Nil =>
                  storeGuarded(pathVar, Variable(newExpr))
              }

              recAnd(pathVar, seq)
              Variable(newExpr)
          }

        case o @ Or(parts) =>
          val partitions = groupWhile(parts)(!requireDecomposition(_))
          partitions.map(orJoin) match {
            case Seq(e) => e
            case seq =>
              val newExpr : Identifier = FreshIdentifier("e", BooleanType, true)
              storeExpr(newExpr)

              def recOr(pathVar: Identifier, partitions: Seq[Expr]): Unit = partitions match {
                case x :: Nil if !requireDecomposition(x) =>
                  storeGuarded(pathVar, Equals(Variable(newExpr), x))

                case x :: xs =>
                  val newBool : Identifier = FreshIdentifier("b", BooleanType, true)
                  storeCond(pathVar, newBool)

                  val xrec = rec(pathVar, x)
                  storeGuarded(pathVar, Equals(Not(Variable(newBool)), xrec))
                  storeGuarded(pathVar, Implies(Not(Variable(newBool)), Variable(newExpr)))

                  recOr(newBool, xs)

                case Nil =>
                  storeGuarded(pathVar, Not(Variable(newExpr)))
              }

              recOr(pathVar, seq)
              Variable(newExpr)
          }

        case i @ IfExpr(cond, thenn, elze) => {
          if(!requireDecomposition(i)) {
            i
          } else {
            val newBool1 : Identifier = FreshIdentifier("b", BooleanType, true)
            val newBool2 : Identifier = FreshIdentifier("b", BooleanType, true)
            val newExpr : Identifier = FreshIdentifier("e", i.getType, true)

            storeCond(pathVar, newBool1)
            storeCond(pathVar, newBool2)

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

          val lid = FreshIdentifier("lambda", bestRealType(l.getType), true)
          val clause = liftedEquals(Variable(lid), l, idArgs, inlineFirst = true)

          val localSubst: Map[Identifier, T] = substMap ++ condVars ++ exprVars ++ lambdaVars
          val clauseSubst: Map[Identifier, T] = localSubst ++ (idArgs zip trArgs)
          val (lambdaConds, lambdaExprs, lambdaTree, lambdaGuarded, lambdaTemplates, lambdaQuants) = mkClauses(pathVar, clause, clauseSubst)

          val ids: (Identifier, T) = lid -> storeLambda(lid)
          val dependencies: Map[Identifier, T] = variablesOf(l).map(id => id -> localSubst(id)).toMap
          val template = LambdaTemplate(ids, encoder, manager, pathVar -> encodedCond(pathVar),
            idArgs zip trArgs, lambdaConds, lambdaExprs, lambdaTree, lambdaGuarded, lambdaQuants, lambdaTemplates, localSubst, dependencies, l)
          registerLambda(template)

          Variable(lid)

        case f @ Forall(args, body) =>
          val TopLevelAnds(conjuncts) = body

          val conjunctQs = conjuncts.map { conjunct =>
            val vars = variablesOf(conjunct)
            val inits = args.map(_.id).filter(vars).toSet
            val (quantifiers, flatConj) = minimalFlattening(inits, conjunct)

            val idQuantifiers : Seq[Identifier] = quantifiers.toSeq
            val trQuantifiers : Seq[T] = idQuantifiers.map(encoder.encodeId)

            val q: Identifier = FreshIdentifier("q", BooleanType, true)
            val q2: Identifier = FreshIdentifier("qo", BooleanType, true)
            val inst: Identifier = FreshIdentifier("inst", BooleanType, true)
            val guard: Identifier = FreshIdentifier("guard", BooleanType, true)

            val clause = Equals(Variable(inst), Implies(Variable(guard), flatConj))

            val qs: (Identifier, T) = q -> encoder.encodeId(q)
            val localSubst: Map[Identifier, T] = substMap ++ condVars ++ exprVars ++ lambdaVars
            val clauseSubst: Map[Identifier, T] = localSubst ++ (idQuantifiers zip trQuantifiers)
            val (p, (qConds, qExprs, qTree, qGuarded, qTemplates, qQuants)) = mkExprClauses(pathVar, flatConj, clauseSubst)
            assert(qQuants.isEmpty, "Unhandled nested quantification in "+clause)

            val allGuarded = qGuarded + (pathVar -> (Seq(
              Equals(Variable(inst), Implies(Variable(guard), p)),
              Equals(Variable(q), And(Variable(q2), Variable(inst)))
            ) ++ qGuarded.getOrElse(pathVar, Seq.empty)))

            val dependencies: Map[Identifier, T] = vars.filterNot(quantifiers).map(id => id -> localSubst(id)).toMap
            val template = QuantificationTemplate[T](encoder, manager, pathVar -> encodedCond(pathVar),
              qs, q2, inst, guard, idQuantifiers zip trQuantifiers, qConds, qExprs, qTree, allGuarded, qTemplates, localSubst,
              dependencies, Forall(quantifiers.toSeq.sortBy(_.uniqueName).map(ValDef(_)), flatConj))
            registerQuantification(template)
            Variable(q)
          }

          andJoin(conjunctQs)

        case Operator(as, r) => r(as.map(a => rec(pathVar, a)))
      }
    }

    val p = rec(pathVar, expr)
    (p, (condVars, exprVars, condTree, guardedExprs, lambdas, quantifications))
  }

}
