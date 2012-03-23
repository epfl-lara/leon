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
        case Block(stmts) => (toFunction(Block(stmts.init)), stmts.last)
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
      val newTExpr = tScope(Tuple(modifiedVars.map(vId => tFun.get(vId) match {
        case Some(newId) => newId.toVariable
        case None => vId.toVariable
      })))
      val newEExpr = eScope(Tuple(modifiedVars.map(vId => eFun.get(vId) match {
        case Some(newId) => newId.toVariable
        case None => vId.toVariable
      })))
      val newIfExpr = IfExpr(cond, newTExpr, newEExpr).setType(newTExpr.getType)
      val scope = ((body: Expr) => LetTuple(freshIds, newIfExpr, body))
      (scope, Map(modifiedVars.zip(freshIds):_*))
    }
    case Block(exprs) => {
      val (headScope, headFun) = toFunction(exprs.head)
      exprs.tail.foldLeft((headScope, headFun))((acc, e) => {
        val (accScope, accFun) = acc
        val (rScope, rFun) = toFunction(e)
        val scope = ((body: Expr) => 
          accScope(replace(accFun.map{case (i1, i2) => (i1.toVariable, i2.toVariable)}, rScope(body))))
        (scope, accFun ++ rFun)
      })
    }
    case _ => sys.error("not supported: " + expr)
    }
    val codeRepresentation = res._1(Block(res._2.map{ case (id1, id2) => Assignment(id1, id2.toVariable)}.toSeq))
    println("res of toFunction on: " + expr + " IS: " + codeRepresentation)
    res
  }

}
