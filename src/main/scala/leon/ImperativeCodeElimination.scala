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
      val (res, _, _) = toFunction(fd.getBody)
      //val ((scope, fun), last) = fd.getBody match {
      //  case Block(stmts, stmt) => (toFunction(Block(stmts.init, stmts.last)), stmt)
      //  case _ => sys.error("not supported")
      //}
      //fd.body = Some(scope(replace(fun.map{case (i1, i2) => (i1.toVariable, i2.toVariable)}, last)))
      fd.body = Some(res)
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
      case IfExpr(cond, tExpr, eExpr) => {
        val (_, tScope, tFun) = toFunction(tExpr)
        val (_, eScope, eFun) = toFunction(eExpr)
        val modifiedVars: Seq[Identifier] = (tFun.keys ++ eFun.keys).toSeq
        val freshIds = modifiedVars.map(id => FreshIdentifier(id.name).setType(id.getType))
        val tupleType = TupleType(freshIds.map(_.getType))
        val newTExpr = tScope(Tuple(modifiedVars.map(vId => tFun.get(vId) match {
          case Some(newId) => newId.toVariable
          case None => vId.toVariable
        })).setType(tupleType))
        val newEExpr = eScope(Tuple(modifiedVars.map(vId => eFun.get(vId) match {
          case Some(newId) => newId.toVariable
          case None => vId.toVariable
        })).setType(tupleType))
        val newIfExpr = IfExpr(cond, newTExpr, newEExpr).setType(newTExpr.getType)
        val scope = ((body: Expr) => {
          val tupleId = FreshIdentifier("t").setType(TupleType(freshIds.map(_.getType)))
          Let(tupleId, newIfExpr, freshIds.zipWithIndex.foldLeft(body)((b, id) => 
                Let(id._1, 
                    TupleSelect(tupleId.toVariable, id._2 + 1).setType(id._1.getType), 
                    b)))
        })
        (Tuple(freshIds.map(_.toVariable)), scope, Map(modifiedVars.zip(freshIds):_*))
      }
      case While(cond, body) => {
        val (_, bodyScope, bodyFun) = toFunction(body)
        val modifiedVars: Seq[Identifier] = bodyFun.keys.toSeq
        val freshIds = modifiedVars.map(id => FreshIdentifier(id.name).setType(id.getType))
        val freshVarDecls = freshIds.map(id => VarDecl(id, id.getType))
        val var2fresh: Map[Expr, Expr] = modifiedVars.zip(freshIds).map(p => (p._1.toVariable, p._2.toVariable)).toMap
        val tupleType = TupleType(freshIds.map(_.getType))
        val funDef = new FunDef(FreshIdentifier("while"), tupleType, freshIds.map(id => VarDecl(id, id.getType)))

        val freshCond = replace(var2fresh, cond)
        val freshBody = bodyScope(FunctionInvocation(funDef, freshIds.map(_.toVariable)))
        val newBody = IfExpr(freshCond, freshBody, Tuple(freshIds.map(_.toVariable))).setType(tupleType)
        funDef.body = Some(newBody)

        val finalVars = modifiedVars.map(id => FreshIdentifier(id.name).setType(id.getType))
        val finalScope = ((body: Expr) => {
          val tupleId = FreshIdentifier("t").setType(tupleType)
          LetDef(
            funDef,
            Let(tupleId, FunctionInvocation(funDef, modifiedVars.map(_.toVariable)), finalVars.zipWithIndex.foldLeft(body)((b, id) => 
                Let(id._1, 
                    TupleSelect(tupleId.toVariable, id._2 + 1).setType(id._1.getType), 
                    b))))
        })

        (UnitLiteral, finalScope, modifiedVars.zip(finalVars).toMap)
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
        (scope(replace(fun.map{ case (i1, i2) => (i1.toVariable, i2.toVariable) }, lastRes)),
         (body: Expr) => scope(lastScope(body)),
         fun ++ lastFun)
      }

      //pure expression (that could still contain side effects as a subexpression)
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
    val codeRepresentation = res._2(Block(res._3.map{ case (id1, id2) => Assignment(id1, id2.toVariable)}.toSeq, res._1))
    println("res of toFunction on: " + expr + " IS: " + codeRepresentation)
    res.asInstanceOf[(Expr, (Expr) => Expr, Map[Identifier, Identifier])]
  }

}
