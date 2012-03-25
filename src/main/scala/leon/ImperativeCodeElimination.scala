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
      val ((scope, fun), last) = fd.getBody match {
        case Block(stmts, stmt) => (toFunction(Block(stmts.init, stmts.last)), stmt)
        case _ => sys.error("not supported")
      }
      fd.body = Some(scope(replace(fun.map{case (i1, i2) => (i1.toVariable, i2.toVariable)}, last)))
    })
    pgm
  }

  //return a "scope" consisting of purely functional code that defines potentially needed 
  //new variables (val, not var) and a mapping for each modified variable (var, not val :) )
  //to their new name defined in the scope
  private def toFunction(expr: Expr): (Expr => Expr, Map[Identifier, Identifier]) = {
    println("toFunction of: " + expr)
    val res = expr match {
      case Assignment(id, e) => {
        val newId = FreshIdentifier(id.name).setType(id.getType)
        val scope = ((body: Expr) => Let(newId, e, body))
        (scope, Map(id -> newId))
      }
      case IfExpr(cond, tExpr, eExpr) => {
        val (tScope, tFun) = toFunction(tExpr)
        val (eScope, eFun) = toFunction(eExpr)
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
        (scope, Map(modifiedVars.zip(freshIds):_*))
      }
      case Block(head::exprs, expr) => {
        val (headScope, headFun) = toFunction(head)
        (exprs:+expr).foldLeft((headScope, headFun))((acc, e) => {
          val (accScope, accFun) = acc
          val (rScope, rFun) = toFunction(e)
          val scope = ((body: Expr) => 
            accScope(replace(accFun.map{case (i1, i2) => (i1.toVariable, i2.toVariable)}, rScope(body))))
          (scope, accFun ++ rFun)
        })
      }
      case _ => sys.error("not supported: " + expr)
    }
    val codeRepresentation = res._1(Block(res._2.map{ case (id1, id2) => Assignment(id1, id2.toVariable)}.toSeq, UnitLiteral))
    println("res of toFunction on: " + expr + " IS: " + codeRepresentation)
    res
  }

}
