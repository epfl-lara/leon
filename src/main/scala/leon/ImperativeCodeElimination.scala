package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

object ImperativeCodeElimination extends Pass {

  val description = "Transform imperative constructs into purely functional code"

  def apply(pgm: Program): Program = {
    val allFuns = pgm.definedFunctions
    allFuns.foreach(fd => {
      val (res, scope, _) = toFunction(fd.getBody)
      fd.body = Some(scope(res))
    })
    pgm
  }

  //return a "scope" consisting of purely functional code that defines potentially needed 
  //new variables (val, not var) and a mapping for each modified variable (var, not val :) )
  //to their new name defined in the scope
  private def toFunction(expr: Expr): (Expr, Expr => Expr, Map[Identifier, Identifier]) = {
    val res = expr match {
      case Assignment(id, e) => {
        val newId = FreshIdentifier(id.name).setType(id.getType)
        val scope = ((body: Expr) => Let(newId, e, body))
        (UnitLiteral, scope, Map(id -> newId))
      }
      case ite@IfExpr(cond, tExpr, eExpr) => {
        val (tRes, tScope, tFun) = toFunction(tExpr)
        val (eRes, eScope, eFun) = toFunction(eExpr)

        val modifiedVars: Seq[Identifier] = (tFun.keys ++ eFun.keys).toSeq
        val resId = FreshIdentifier("res").setType(ite.getType)
        val freshIds = modifiedVars.map(id => FreshIdentifier(id.name).setType(id.getType))
        val iteType = if(modifiedVars.isEmpty) resId.getType else TupleType(resId.getType +: freshIds.map(_.getType))

        val thenVal = if(modifiedVars.isEmpty) tRes else Tuple(tRes +: modifiedVars.map(vId => tFun.get(vId) match {
          case Some(newId) => newId.toVariable
          case None => vId.toVariable
        }))
        thenVal.setType(iteType)

        val elseVal = if(modifiedVars.isEmpty) eRes else Tuple(eRes +: modifiedVars.map(vId => eFun.get(vId) match {
          case Some(newId) => newId.toVariable
          case None => vId.toVariable
        }))
        elseVal.setType(iteType)

        val iteExpr = IfExpr(cond, tScope(thenVal), eScope(elseVal)).setType(iteType)

        val scope = ((body: Expr) => {
          val tupleId = FreshIdentifier("t").setType(iteType)
          Let(tupleId, iteExpr, 
              if(freshIds.isEmpty)
                Let(resId, tupleId.toVariable, body)
              else
                Let(resId, TupleSelect(tupleId.toVariable, 1),
                  freshIds.zipWithIndex.foldLeft(body)((b, id) => 
                    Let(id._1, 
                      TupleSelect(tupleId.toVariable, id._2 + 2).setType(id._1.getType), 
                      b))))
        })

        (resId.toVariable, scope, modifiedVars.zip(freshIds).toMap)
      }
      case wh@While(cond, body) => {
        val (_, bodyScope, bodyFun) = toFunction(body)
        val modifiedVars: Seq[Identifier] = bodyFun.keys.toSeq

        if(modifiedVars.isEmpty)
          (UnitLiteral, (b: Expr) => b, Map())
        else {
          val whileFunVars = modifiedVars.map(id => FreshIdentifier(id.name).setType(id.getType))
          val whileFunVarDecls = whileFunVars.map(id => VarDecl(id, id.getType))
          val whileFunReturnType = if(whileFunVars.size == 1) whileFunVars.head.getType else TupleType(whileFunVars.map(_.getType))
          val whileFunDef = new FunDef(FreshIdentifier("while"), whileFunReturnType, whileFunVarDecls)
          
          val modifiedVars2WhileFunVars: Map[Expr, Expr] = modifiedVars.zip(whileFunVars).map(p => (p._1.toVariable, p._2.toVariable)).toMap
          val whileFunCond = replace(modifiedVars2WhileFunVars, cond)
          val whileFunRecursiveCall = replace(modifiedVars2WhileFunVars, bodyScope(FunctionInvocation(whileFunDef, modifiedVars.map(id => bodyFun(id).toVariable))))
          val whileFunBaseCase = (if(whileFunVars.size == 1) whileFunVars.head.toVariable else Tuple(whileFunVars.map(_.toVariable))).setType(whileFunReturnType)
          val whileFunBody = IfExpr(whileFunCond, whileFunRecursiveCall, whileFunBaseCase).setType(whileFunReturnType)
          whileFunDef.body = Some(whileFunBody)

          val resVar = ResultVariable().setType(whileFunReturnType)
          val whileFunVars2ResultVars: Map[Expr, Expr] = 
            if(whileFunVars.size == 1) 
              Map(whileFunVars.head.toVariable -> resVar)
            else
              whileFunVars.zipWithIndex.map{ case (v, i) => (v.toVariable, TupleSelect(resVar, i+1).setType(v.getType)) }.toMap
          val modifiedVars2ResultVars: Map[Expr, Expr] = modifiedVars.map(v => (v.toVariable, modifiedVars2WhileFunVars(v.toVariable))).toMap

          val trivialPostcondition: Option[Expr] = Some(Not(replace(whileFunVars2ResultVars, whileFunCond)))
          val invariantPrecondition: Option[Expr] = wh.invariant.map(expr => replace(modifiedVars2WhileFunVars, expr))
          whileFunDef.precondition = invariantPrecondition
          whileFunDef.postcondition = trivialPostcondition.map(expr => 
              And(expr, invariantPrecondition match { 
                case Some(e) => replace(modifiedVars2ResultVars, e)
                case None => BooleanLiteral(true)
              }))

          val finalVars = modifiedVars.map(id => FreshIdentifier(id.name).setType(id.getType))
          val finalScope = ((body: Expr) => {
            val tupleId = FreshIdentifier("t").setType(whileFunReturnType)
            LetDef(
              whileFunDef,
              Let(tupleId, 
                  FunctionInvocation(whileFunDef, modifiedVars.map(_.toVariable)), 
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
      case Block(head::exprs, expr) => {
        val (_, headScope, headFun) = toFunction(head)
        val (scope, fun) = exprs.foldLeft((headScope, headFun))((acc, e) => {
          val (accScope, accFun) = acc
          val (_, rScope, rFun) = toFunction(e)
          val scope = ((body: Expr) => 
            accScope(replace(accFun.map{case (i1, i2) => (i1.toVariable, i2.toVariable)}, rScope(body))))
          (scope, accFun ++ rFun)
        })
        val (lastRes, lastScope, lastFun) = toFunction(expr)
        (replace(fun.map{ case (i1, i2) => (i1.toVariable, i2.toVariable) }, lastRes),
         (body: Expr) => scope(lastScope(body)),
         fun ++ lastFun)
      }

      //pure expression (that could still contain side effects as a subexpression)
      case Let(id, e, b) => {
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)
        (bodyRes, (b: Expr) => Let(id, e, bodyScope(b)), bodyFun)
      }
      case LetDef(fd, b) => {
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)
        (bodyRes, (b: Expr) => LetDef(fd, bodyScope(b)), bodyFun)
      }
      case n @ NAryOperator(args, recons) => {
        val (recArgs, scope, fun) = args.foldLeft((Seq[Expr](), (body: Expr) => body, Map[Identifier, Identifier]()))((acc, arg) => {
          val (accArgs, scope, fun) = acc
          val (argVal, argScope, argFun) = toFunction(arg)
          val argInScope = scope(replace(fun.map(ids => (ids._1.toVariable, ids._2.toVariable)), argVal))
          (accArgs :+ argInScope, (body: Expr) => scope(argScope(body)), fun ++ argFun)
        })
        (recons(recArgs), scope, fun)
      }
      case b @ BinaryOperator(a1, a2, recons) => {
        val (argVal1, argScope1, argFun1) = toFunction(a1)
        val (argVal2, argScope2, argFun2) = toFunction(a2)
        (recons(argVal1, argVal2), (body: Expr) => argScope1(argScope2(body)), argFun1 ++ argFun2)
      }
      case u @ UnaryOperator(a, recons) => {
        val (argVal, argScope, argFun) = toFunction(a)
        (recons(a), argScope, argFun)
      }
      case (t: Terminal) => (t, (body: Expr) => body, Map())
      case m @ MatchExpr(scrut, cses) => sys.error("not supported: " + expr)
      case _ => sys.error("not supported: " + expr)
    }
    //val codeRepresentation = res._2(Block(res._3.map{ case (id1, id2) => Assignment(id1, id2.toVariable)}.toSeq, res._1))
    //println("res of toFunction on: " + expr + " IS: " + codeRepresentation)
    res.asInstanceOf[(Expr, (Expr) => Expr, Map[Identifier, Identifier])]
  }

}
