/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package xlang

import leon.TransformationPhase
import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.Extractors._
import leon.purescala.TypeTrees._
import leon.purescala.TreeOps._
import leon.xlang.Trees._

object ImperativeCodeElimination extends LeonPhase[Program, (Program, Set[FunDef])] {

  val name = "Imperative Code Elimination"
  val description = "Transform imperative constructs into purely functional code"

  private var varInScope = Set[Identifier]()
  private var parent: FunDef = null //the enclosing fundef
  private var wasLoop: Set[FunDef] = null //record FunDef that are the transformation of loops

  def run(ctx: LeonContext)(pgm: Program): (Program, Set[FunDef]) = {
    varInScope = Set()
    wasLoop = Set()
    parent = null

    val allFuns = pgm.definedFunctions
    allFuns.foreach(fd => fd.body.map(body => {
      parent = fd
      val (res, scope, _) = toFunction(body)
      fd.body = Some(scope(res))
    }))
    (pgm, wasLoop)
  }

  //return a "scope" consisting of purely functional code that defines potentially needed 
  //new variables (val, not var) and a mapping for each modified variable (var, not val :) )
  //to their new name defined in the scope. The first returned valued is the value of the expression
  //that should be introduced as such in the returned scope (the val already refers to the new names)
  private def toFunction(expr: Expr): (Expr, Expr => Expr, Map[Identifier, Identifier]) = {
    val res = expr match {
      case LetVar(id, e, b) => {
        val newId = FreshIdentifier(id.name).setType(id.getType)
        val (rhsVal, rhsScope, rhsFun) = toFunction(e)
        varInScope += id
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)
        varInScope -= id
        val scope = (body: Expr) => rhsScope(Let(newId, rhsVal, replaceNames(rhsFun + (id -> newId), bodyScope(body))))
        (bodyRes, scope, (rhsFun + (id -> newId)) ++ bodyFun)
      }
      case Assignment(id, e) => {
        assert(varInScope.contains(id))
        val newId = FreshIdentifier(id.name).setType(id.getType)
        val (rhsVal, rhsScope, rhsFun) = toFunction(e)
        val scope = (body: Expr) => rhsScope(Let(newId, rhsVal, body))
        (UnitLiteral, scope, rhsFun + (id -> newId))
      }

      case ite@IfExpr(cond, tExpr, eExpr) => {
        val (cRes, cScope, cFun) = toFunction(cond)
        val (tRes, tScope, tFun) = toFunction(tExpr)
        val (eRes, eScope, eFun) = toFunction(eExpr)

        val iteRType = leastUpperBound(tRes.getType, eRes.getType).get

        val modifiedVars: Seq[Identifier] = (tFun.keys ++ eFun.keys).toSet.intersect(varInScope).toSeq
        val resId = FreshIdentifier("res").setType(iteRType)
        val freshIds = modifiedVars.map(id => FreshIdentifier(id.name).setType(id.getType))
        val iteType = if(modifiedVars.isEmpty) resId.getType else TupleType(resId.getType +: freshIds.map(_.getType))

        val thenVal = if(modifiedVars.isEmpty) tRes else Tuple(tRes +: modifiedVars.map(vId => tFun.get(vId) match {
          case Some(newId) => newId.toVariable
          case None => vId.toVariable
        })).setType(iteType)

        val elseVal = if(modifiedVars.isEmpty) eRes else Tuple(eRes +: modifiedVars.map(vId => eFun.get(vId) match {
          case Some(newId) => newId.toVariable
          case None => vId.toVariable
        })).setType(iteType)

        val iteExpr = IfExpr(cRes, replaceNames(cFun, tScope(thenVal)), replaceNames(cFun, eScope(elseVal))).setType(iteType)

        val scope = ((body: Expr) => {
          val tupleId = FreshIdentifier("t").setType(iteType)
          cScope(
            Let(tupleId, iteExpr, 
              if(freshIds.isEmpty)
                Let(resId, tupleId.toVariable, body)
              else
                Let(resId, TupleSelect(tupleId.toVariable, 1).setType(iteRType),
                  freshIds.zipWithIndex.foldLeft(body)((b, id) => 
                    Let(id._1, 
                      TupleSelect(tupleId.toVariable, id._2 + 2).setType(id._1.getType), 
                      b)))))
        })

        (resId.toVariable, scope, cFun ++ modifiedVars.zip(freshIds).toMap)
      }

      case m @ MatchExpr(scrut, cses) => {
        val csesRhs = cses.map(_.rhs) //we can ignore pattern, and the guard is required to be pure
        val (csesRes, csesScope, csesFun) = csesRhs.map(toFunction).unzip3
        val (scrutRes, scrutScope, scrutFun) = toFunction(scrut)

        val modifiedVars: Seq[Identifier] = csesFun.toSet.flatMap((m: Map[Identifier, Identifier]) => m.keys).intersect(varInScope).toSeq
        val resId = FreshIdentifier("res").setType(m.getType)
        val freshIds = modifiedVars.map(id => FreshIdentifier(id.name).setType(id.getType))
        val matchType = if(modifiedVars.isEmpty) resId.getType else TupleType(resId.getType +: freshIds.map(_.getType))

        val csesVals = csesRes.zip(csesFun).map{ 
          case (cRes, cFun) => if(modifiedVars.isEmpty) cRes else Tuple(cRes +: modifiedVars.map(vId => cFun.get(vId) match {
            case Some(newId) => newId.toVariable
            case None => vId.toVariable
          })).setType(matchType)
        }

        val newRhs = csesVals.zip(csesScope).map{ 
          case (cVal, cScope) => replaceNames(scrutFun, cScope(cVal))
        }
        val matchExpr = MatchExpr(scrutRes, cses.zip(newRhs).map{
          case (SimpleCase(pat, _), newRhs) => SimpleCase(pat, newRhs)
          case (GuardedCase(pat, guard, _), newRhs) => GuardedCase(pat, replaceNames(scrutFun, guard), newRhs)
        }).setType(matchType).setPosInfo(m)

        val scope = ((body: Expr) => {
          val tupleId = FreshIdentifier("t").setType(matchType)
          scrutScope(
            Let(tupleId, matchExpr, 
              if(freshIds.isEmpty)
                Let(resId, tupleId.toVariable, body)
              else
                Let(resId, TupleSelect(tupleId.toVariable, 1),
                  freshIds.zipWithIndex.foldLeft(body)((b, id) => 
                    Let(id._1, 
                      TupleSelect(tupleId.toVariable, id._2 + 2).setType(id._1.getType), 
                      b)))))
        })

        (resId.toVariable, scope, scrutFun ++ modifiedVars.zip(freshIds).toMap)
      }
      case wh@While(cond, body) => {
        val (condRes, condScope, condFun) = toFunction(cond)
        val (_, bodyScope, bodyFun) = toFunction(body)
        val condBodyFun = condFun ++ bodyFun

        val modifiedVars: Seq[Identifier] = condBodyFun.keys.toSet.intersect(varInScope).toSeq

        if(modifiedVars.isEmpty)
          (UnitLiteral, (b: Expr) => b, Map())
        else {
          val whileFunVars = modifiedVars.map(id => FreshIdentifier(id.name).setType(id.getType))
          val modifiedVars2WhileFunVars = modifiedVars.zip(whileFunVars).toMap
          val whileFunVarDecls = whileFunVars.map(id => VarDecl(id, id.getType))
          val whileFunReturnType = if(whileFunVars.size == 1) whileFunVars.head.getType else TupleType(whileFunVars.map(_.getType))
          val whileFunDef = new FunDef(FreshIdentifier(parent.id.name), whileFunReturnType, whileFunVarDecls).setPosInfo(wh)
          wasLoop += whileFunDef
          
          val whileFunCond = condRes
          val whileFunRecursiveCall = replaceNames(condFun,
            bodyScope(FunctionInvocation(whileFunDef, modifiedVars.map(id => condBodyFun(id).toVariable)).setPosInfo(wh)))
          val whileFunBaseCase =
            (if(whileFunVars.size == 1) 
                condFun.get(modifiedVars.head).getOrElse(whileFunVars.head).toVariable
             else 
                Tuple(modifiedVars.map(id => condFun.get(id).getOrElse(modifiedVars2WhileFunVars(id)).toVariable))
            ).setType(whileFunReturnType)
          val whileFunBody = replaceNames(modifiedVars2WhileFunVars, 
            condScope(IfExpr(whileFunCond, whileFunRecursiveCall, whileFunBaseCase).setType(whileFunReturnType)))
          whileFunDef.body = Some(whileFunBody)

          val resVar = Variable(FreshIdentifier("res").setType(whileFunReturnType))
          val whileFunVars2ResultVars: Map[Expr, Expr] = 
            if(whileFunVars.size == 1) 
              Map(whileFunVars.head.toVariable -> resVar)
            else
              whileFunVars.zipWithIndex.map{ case (v, i) => (v.toVariable, TupleSelect(resVar, i+1).setType(v.getType)) }.toMap
          val modifiedVars2ResultVars: Map[Expr, Expr]  = modifiedVars.map(id => 
            (id.toVariable, whileFunVars2ResultVars(modifiedVars2WhileFunVars(id).toVariable))).toMap

          //the mapping of the trivial post condition variables depends on whether the condition has had some side effect
          val trivialPostcondition: Option[Expr] = Some(Not(replace(
            modifiedVars.map(id => (condFun.get(id).getOrElse(id).toVariable, modifiedVars2ResultVars(id.toVariable))).toMap,
            whileFunCond)))
          val invariantPrecondition: Option[Expr] = wh.invariant.map(expr => replaceNames(modifiedVars2WhileFunVars, expr))
          val invariantPostcondition: Option[Expr] = wh.invariant.map(expr => replace(modifiedVars2ResultVars, expr))
          whileFunDef.precondition = invariantPrecondition
          whileFunDef.postcondition = trivialPostcondition.map(expr => 
              (resVar.id, And(expr, invariantPostcondition match { 
                case Some(e) => e
                case None => BooleanLiteral(true)
              })))

          val finalVars = modifiedVars.map(id => FreshIdentifier(id.name).setType(id.getType))
          val finalScope = ((body: Expr) => {
            val tupleId = FreshIdentifier("t").setType(whileFunReturnType)
            LetDef(
              whileFunDef,
              Let(tupleId, 
                  FunctionInvocation(whileFunDef, modifiedVars.map(_.toVariable)).setPosInfo(wh), 
                  if(finalVars.size == 1)
                    Let(finalVars.head, tupleId.toVariable, body)
                  else
                    finalVars.zipWithIndex.foldLeft(body)((b, id) => 
                      Let(id._1, 
                        TupleSelect(tupleId.toVariable, id._2 + 1).setType(id._1.getType), 
                        b))))
          })

          (UnitLiteral, finalScope, modifiedVars.zip(finalVars).toMap)
        }
      }

      case Block(Seq(), expr) => toFunction(expr)
      case Block(exprs, expr) => {
        val (scope, fun) = exprs.foldRight((body: Expr) => body, Map[Identifier, Identifier]())((e, acc) => {
          val (accScope, accFun) = acc
          val (_, rScope, rFun) = toFunction(e)
          val scope = (body: Expr) => rScope(replaceNames(rFun, accScope(body)))
          (scope, rFun ++ accFun)
        })
        val (lastRes, lastScope, lastFun) = toFunction(expr)
        val finalFun = fun ++ lastFun
        (replaceNames(finalFun, lastRes),
         (body: Expr) => scope(replaceNames(fun, lastScope(body))),
         finalFun)
      }

      //pure expression (that could still contain side effects as a subexpression) (evaluation order is from left to right)
      case Let(id, e, b) => {
        val (bindRes, bindScope, bindFun) = toFunction(e)
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)
        (bodyRes, 
         (b2: Expr) => bindScope(Let(id, bindRes, replaceNames(bindFun, bodyScope(b2)))), 
         bindFun ++ bodyFun)
      }
      case LetDef(fd, b) => {
        //Recall that here the nested function should not access mutable variables from an outside scope
        val newFd = fd.body match {
          case Some(b) =>
            val (fdRes, fdScope, fdFun) = toFunction(b)
            fd.body = Some(fdScope(fdRes))
            fd
          case None =>
            fd
        }
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)
        (bodyRes, (b2: Expr) => LetDef(newFd, bodyScope(b2)), bodyFun)
      }
      case c @ Choose(ids, b) => {
        //Recall that Choose cannot mutate variables from the scope
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)
        (bodyRes, (b2: Expr) => Choose(ids, bodyScope(b2)).setPosInfo(c), bodyFun)
      }
      case n @ NAryOperator(Seq(), recons) => (n, (body: Expr) => body, Map())
      case n @ NAryOperator(args, recons) => {
        val (recArgs, scope, fun) = args.foldRight((Seq[Expr](), (body: Expr) => body, Map[Identifier, Identifier]()))((arg, acc) => {
          val (accArgs, accScope, accFun) = acc
          val (argVal, argScope, argFun) = toFunction(arg)
          val newScope = (body: Expr) => argScope(replaceNames(argFun, accScope(body)))
          (argVal +: accArgs, newScope, argFun ++ accFun)
        })
        (recons(recArgs).setType(n.getType), scope, fun)
      }
      case b @ BinaryOperator(a1, a2, recons) => {
        val (argVal1, argScope1, argFun1) = toFunction(a1)
        val (argVal2, argScope2, argFun2) = toFunction(a2)
        val scope = (body: Expr) => {
          val rhs = argScope2(replaceNames(argFun2, body))
          val lhs = argScope1(replaceNames(argFun1, rhs))
          lhs
        }
        (recons(argVal1, argVal2).setType(b.getType), scope, argFun1 ++ argFun2)
      }
      case u @ UnaryOperator(a, recons) => {
        val (argVal, argScope, argFun) = toFunction(a)
        (recons(argVal).setType(u.getType), argScope, argFun)
      }
      case (t: Terminal) => (t, (body: Expr) => body, Map())


      case _ => sys.error("not supported: " + expr)
    }
    //val codeRepresentation = res._2(Block(res._3.map{ case (id1, id2) => Assignment(id1, id2.toVariable)}.toSeq, res._1))
    //println("res of toFunction on: " + expr + " IS: " + codeRepresentation)
    res.asInstanceOf[(Expr, (Expr) => Expr, Map[Identifier, Identifier])] //need cast because it seems that res first map type is _ <: Identifier instead of Identifier
  }

  def replaceNames(fun: Map[Identifier, Identifier], expr: Expr) = replace(fun.map(ids => (ids._1.toVariable, ids._2.toVariable)), expr)

}
