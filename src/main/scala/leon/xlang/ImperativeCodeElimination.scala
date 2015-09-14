/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package xlang

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Extractors._
import leon.purescala.Constructors._
import leon.purescala.ExprOps._
import leon.purescala.TypeOps._
import leon.xlang.Expressions._

object ImperativeCodeElimination extends UnitPhase[Program] {

  val name = "Imperative Code Elimination"
  val description = "Transform imperative constructs into purely functional code"

  def apply(ctx: LeonContext, pgm: Program): Unit = {
    for {
      fd <- pgm.definedFunctions
      body <- fd.body
    } {
      val (res, scope, _) = toFunction(body)(State(fd, Set()))
      fd.body = Some(scope(res))
    }
  }

  case class State(parent: FunDef, varsInScope: Set[Identifier]) {
    def withVar(i: Identifier) = copy(varsInScope = varsInScope + i)
  }

  //return a "scope" consisting of purely functional code that defines potentially needed 
  //new variables (val, not var) and a mapping for each modified variable (var, not val :) )
  //to their new name defined in the scope. The first returned valued is the value of the expression
  //that should be introduced as such in the returned scope (the val already refers to the new names)
  private def toFunction(expr: Expr)(implicit state: State): (Expr, Expr => Expr, Map[Identifier, Identifier]) = {
    import state._
    expr match {
      case LetVar(id, e, b) =>
        val newId = id.freshen
        val (rhsVal, rhsScope, rhsFun) = toFunction(e)
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)(state.withVar(id))
        val scope = (body: Expr) => rhsScope(Let(newId, rhsVal, replaceNames(rhsFun + (id -> newId), bodyScope(body))).copiedFrom(expr))
        (bodyRes, scope, (rhsFun + (id -> newId)) ++ bodyFun)
 
      case Assignment(id, e) =>
        assert(varsInScope.contains(id))
        val newId = id.freshen
        val (rhsVal, rhsScope, rhsFun) = toFunction(e)
        val scope = (body: Expr) => rhsScope(Let(newId, rhsVal, body).copiedFrom(expr))
        (UnitLiteral(), scope, rhsFun + (id -> newId))

      case ite@IfExpr(cond, tExpr, eExpr) =>
        val (cRes, cScope, cFun) = toFunction(cond)
        val (tRes, tScope, tFun) = toFunction(tExpr)
        val (eRes, eScope, eFun) = toFunction(eExpr)

        val iteRType = leastUpperBound(tRes.getType, eRes.getType).get

        val modifiedVars: Seq[Identifier] = (tFun.keys ++ eFun.keys).toSet.intersect(varsInScope).toSeq
        val resId = FreshIdentifier("res", iteRType)
        val freshIds = modifiedVars.map( _.freshen )
        val iteType = tupleTypeWrap(resId.getType +: freshIds.map(_.getType))

        val thenVal = tupleWrap(tRes +: modifiedVars.map(vId => tFun.getOrElse(vId, vId).toVariable))
        val elseVal = tupleWrap(eRes +: modifiedVars.map(vId => eFun.getOrElse(vId, vId).toVariable))
        val iteExpr = IfExpr(cRes, replaceNames(cFun, tScope(thenVal)), replaceNames(cFun, eScope(elseVal))).copiedFrom(ite)

        val scope = (body: Expr) => {
          val tupleId = FreshIdentifier("t", iteType)
          cScope(Let(tupleId, iteExpr, Let(
            resId,
            tupleSelect(tupleId.toVariable, 1, modifiedVars.nonEmpty),
            freshIds.zipWithIndex.foldLeft(body)((b, id) =>
              Let(id._1, tupleSelect(tupleId.toVariable, id._2 + 2, true), b)
            ))
          ).copiedFrom(expr))
        }

        (resId.toVariable, scope, cFun ++ modifiedVars.zip(freshIds).toMap)

      case m @ MatchExpr(scrut, cses) =>
        val csesRhs = cses.map(_.rhs) //we can ignore pattern, and the guard is required to be pure
        val (csesRes, csesScope, csesFun) = csesRhs.map(toFunction).unzip3
        val (scrutRes, scrutScope, scrutFun) = toFunction(scrut)

        val modifiedVars: Seq[Identifier] = csesFun.toSet.flatMap((m: Map[Identifier, Identifier]) => m.keys).intersect(varsInScope).toSeq
        val resId = FreshIdentifier("res", m.getType)
        val freshIds = modifiedVars.map(id => FreshIdentifier(id.name, id.getType))
        val matchType = tupleTypeWrap(resId.getType +: freshIds.map(_.getType))

        val csesVals = csesRes.zip(csesFun).map {
          case (cRes, cFun) => tupleWrap(cRes +: modifiedVars.map(vId => cFun.getOrElse(vId, vId).toVariable))
        }

        val newRhs = csesVals.zip(csesScope).map {
          case (cVal, cScope) => replaceNames(scrutFun, cScope(cVal))
        }
        val matchE = matchExpr(scrutRes, cses.zip(newRhs).map {
          case (mc @ MatchCase(pat, guard, _), newRhs) =>
            MatchCase(pat, guard map { replaceNames(scrutFun, _) }, newRhs).setPos(mc)
        }).setPos(m)

        val scope = (body: Expr) => {
          val tupleId = FreshIdentifier("t", matchType)
          scrutScope(
            Let(tupleId, matchE,
              Let(resId, tupleSelect(tupleId.toVariable, 1, freshIds.nonEmpty),
                freshIds.zipWithIndex.foldLeft(body)((b, id) =>
                  Let(id._1, tupleSelect(tupleId.toVariable, id._2 + 2, true), b)
                )
              )
            )
          )
        }

        (resId.toVariable, scope, scrutFun ++ modifiedVars.zip(freshIds).toMap)
 
      case wh@While(cond, body) =>
        val (condRes, condScope, condFun) = toFunction(cond)
        val (_, bodyScope, bodyFun) = toFunction(body)
        val condBodyFun = condFun ++ bodyFun

        val modifiedVars: Seq[Identifier] = condBodyFun.keys.toSet.intersect(varsInScope).toSeq

        if(modifiedVars.isEmpty)
          (UnitLiteral(), (b: Expr) => b, Map())
        else {
          val whileFunVars = modifiedVars.map(id => FreshIdentifier(id.name, id.getType))
          val modifiedVars2WhileFunVars = modifiedVars.zip(whileFunVars).toMap
          val whileFunValDefs = whileFunVars.map(ValDef(_))
          val whileFunReturnType = tupleTypeWrap(whileFunVars.map(_.getType))
          val whileFunDef = new FunDef(parent.id.freshen, Nil, whileFunReturnType, whileFunValDefs).setPos(wh)
          whileFunDef.addFlag(IsLoop(parent))
          
          val whileFunCond = condScope(condRes)
          val whileFunRecursiveCall = replaceNames(condFun,
            bodyScope(FunctionInvocation(whileFunDef.typed, modifiedVars.map(id => condBodyFun(id).toVariable)).setPos(wh)))
          val whileFunBaseCase =
            tupleWrap(modifiedVars.map(id => condFun.getOrElse(id, modifiedVars2WhileFunVars(id)).toVariable))
          val whileFunBody = replaceNames(modifiedVars2WhileFunVars, 
            condScope(IfExpr(whileFunCond, whileFunRecursiveCall, whileFunBaseCase)))
          whileFunDef.body = Some(whileFunBody)

          val resVar = Variable(FreshIdentifier("res", whileFunReturnType))
          val whileFunVars2ResultVars: Map[Expr, Expr] = 
            whileFunVars.zipWithIndex.map{ case (v, i) => 
              (v.toVariable, tupleSelect(resVar, i+1, whileFunVars.size))
            }.toMap
          val modifiedVars2ResultVars: Map[Expr, Expr]  = modifiedVars.map(id => 
            (id.toVariable, whileFunVars2ResultVars(modifiedVars2WhileFunVars(id).toVariable))).toMap

          //the mapping of the trivial post condition variables depends on whether the condition has had some side effect
          val trivialPostcondition: Option[Expr] = Some(Not(replace(
            modifiedVars.map(id => (condFun.getOrElse(id, id).toVariable, modifiedVars2ResultVars(id.toVariable))).toMap,
            whileFunCond)))
          val invariantPrecondition: Option[Expr] = wh.invariant.map(expr => replaceNames(modifiedVars2WhileFunVars, expr))
          val invariantPostcondition: Option[Expr] = wh.invariant.map(expr => replace(modifiedVars2ResultVars, expr))
          whileFunDef.precondition = invariantPrecondition
          whileFunDef.postcondition = trivialPostcondition.map( expr => 
            Lambda(
              Seq(ValDef(resVar.id)), 
              and(expr, invariantPostcondition.getOrElse(BooleanLiteral(true))).setPos(wh)
            ).setPos(wh)
          )

          val finalVars = modifiedVars.map(_.freshen)
          val finalScope = (body: Expr) => {
            val tupleId = FreshIdentifier("t", whileFunReturnType)
            LetDef(whileFunDef, Let(
              tupleId,
              FunctionInvocation(whileFunDef.typed, modifiedVars.map(_.toVariable)).setPos(wh),
              finalVars.zipWithIndex.foldLeft(body) { (b, id) =>
                Let(id._1, tupleSelect(tupleId.toVariable, id._2 + 1, finalVars.size), b)
              }
            ))
          }

          (UnitLiteral(), finalScope, modifiedVars.zip(finalVars).toMap)
        }

      case Block(Seq(), expr) =>
        toFunction(expr)

      case Block(exprs, expr) =>
        val (scope, fun) = exprs.foldRight((body: Expr) => body, Map[Identifier, Identifier]())((e, acc) => {
          val (accScope, accFun) = acc
          val (_, rScope, rFun) = toFunction(e)
          val scope = (body: Expr) => {
            val withoutPrec = rScope(replaceNames(rFun, accScope(body)))
            e match {
              case FunctionInvocation(tfd, args) if tfd.hasPrecondition =>
                Assert(tfd.withParamSubst(args, tfd.precondition.get), Some("Precondition failed"), withoutPrec)
              case _ =>
                withoutPrec
            }

          }
          (scope, rFun ++ accFun)
        })
        val (lastRes, lastScope, lastFun) = toFunction(expr)
        val finalFun = fun ++ lastFun
        (
          replaceNames(finalFun, lastRes),
          (body: Expr) => scope(replaceNames(fun, lastScope(body))),
          finalFun
        )

      //pure expression (that could still contain side effects as a subexpression) (evaluation order is from left to right)
      case Let(id, e, b) =>
        val (bindRes, bindScope, bindFun) = toFunction(e)
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)
        (
          bodyRes, 
          (b2: Expr) => bindScope(Let(id, bindRes, replaceNames(bindFun, bodyScope(b2))).copiedFrom(expr)), 
          bindFun ++ bodyFun
        )

      case LetDef(fd, b) =>
        //Recall that here the nested function should not access mutable variables from an outside scope
        fd.body.foreach { bd =>
          val (fdRes, fdScope, _) = toFunction(bd)
          fd.body = Some(fdScope(fdRes))
        }
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)
        (bodyRes, (b2: Expr) => LetDef(fd, bodyScope(b2)).copiedFrom(expr), bodyFun)

      case c @ Choose(b) =>
        //Recall that Choose cannot mutate variables from the scope
        (c, (b2: Expr) => b2, Map())

      case And(args) =>
        val ifExpr = args.reduceRight((el, acc) => IfExpr(el, acc, BooleanLiteral(false)))
        toFunction(ifExpr)

      case Or(args) =>
        val ifExpr = args.reduceRight((el, acc) => IfExpr(el, BooleanLiteral(true), acc))
        toFunction(ifExpr)

      case n @ Operator(args, recons) =>
        val (recArgs, scope, fun) = args.foldRight((Seq[Expr](), (body: Expr) => body, Map[Identifier, Identifier]()))((arg, acc) => {
          val (accArgs, accScope, accFun) = acc
          val (argVal, argScope, argFun) = toFunction(arg)
          val newScope = (body: Expr) => argScope(replaceNames(argFun, accScope(body)))
          (argVal +: accArgs, newScope, argFun ++ accFun)
        })
        (recons(recArgs).copiedFrom(n), scope, fun)

      case _ =>
        sys.error("not supported: " + expr)
    }
  }

  def replaceNames(fun: Map[Identifier, Identifier], expr: Expr) = replaceFromIDs(fun mapValues Variable, expr)

}
