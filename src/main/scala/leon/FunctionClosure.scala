package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

object FunctionClosure extends Pass {

  val description = "Closing function with its scoping variables"

  def apply(program: Program): Program = {
    val funDefs = program.definedFunctions
    funDefs.foreach(fd =>
      fd.body = Some(functionClosure(fd.getBody, fd.args.map(_.id).toSet))
    )
    program
  }

  private def functionClosure(expr: Expr, bindedVars: Set[Identifier]): Expr = expr match {
    case l @ LetDef(FunDef(id, rt, varDecl, Some(funBody), _, _), rest) => {
      //TODO: I am assuming each var decl in a new function is having a unique, different ID
      val vars = variablesOf(funBody)
      val capturedVars = vars.intersect(bindedVars).toSeq // this should be the variable used that are in the scope
      val freshVars: Map[Identifier, Identifier] = capturedVars.map(v => (v, FreshIdentifier(v.name).setType(v.getType))).toMap
      val freshBody = replace(freshVars.map{ case (v1, v2) => (v1.toVariable, v2.toVariable) }, funBody)
      val extraVarDecls = freshVars.map{ case (_, v2) => VarDecl(v2, v2.getType) }
      val newVarDecls = varDecl ++ extraVarDecls
      val newFunDef = new FunDef(id, rt, newVarDecls)
      def substFunInvocInDef(expr: Expr): Option[Expr] = expr match {
        case FunctionInvocation(fd, args) if fd.id == id => Some(FunctionInvocation(newFunDef, args ++ extraVarDecls.map(_.id.toVariable)))
        case _ => None
      }
      val recBody = functionClosure(freshBody, bindedVars ++ newVarDecls.map(_.id))
      val recBody2 = searchAndReplaceDFS(substFunInvocInDef)(recBody)
      newFunDef.body = Some(recBody2)
      def substFunInvocInRest(expr: Expr): Option[Expr] = expr match {
        case FunctionInvocation(fd, args) if fd.id == id => Some(FunctionInvocation(newFunDef, args ++ capturedVars.map(_.toVariable)))
        case _ => None
      }
      val recRest = functionClosure(rest, bindedVars)
      val recRest2 = searchAndReplaceDFS(substFunInvocInRest)(recRest)
      LetDef(newFunDef, recRest2).setType(l.getType)
    }
    case l @ Let(i,e,b) => {
      val re = functionClosure(e, bindedVars)
      val rb = functionClosure(b, bindedVars + i)
      Let(i, re, rb).setType(l.getType)
    }
    case n @ NAryOperator(args, recons) => {
      var change = false
      val rargs = args.map(a => functionClosure(a, bindedVars))
      recons(rargs).setType(n.getType)
    }
    case b @ BinaryOperator(t1,t2,recons) => {
      val r1 = functionClosure(t1, bindedVars)
      val r2 = functionClosure(t2, bindedVars)
      recons(r1,r2).setType(b.getType)
    }
    case u @ UnaryOperator(t,recons) => {
      val r = functionClosure(t, bindedVars)
      recons(r).setType(u.getType)
    }
    case i @ IfExpr(t1,t2,t3) => {
      val r1 = functionClosure(t1, bindedVars)
      val r2 = functionClosure(t2, bindedVars)
      val r3 = functionClosure(t3, bindedVars)
      IfExpr(r1, r2, r3).setType(i.getType)
    }
    case m @ MatchExpr(scrut,cses) => sys.error("Will see")//MatchExpr(rec(scrut), cses.map(inCase(_))).setType(m.getType).setPosInfo(m)
    case t if t.isInstanceOf[Terminal] => t
    case unhandled => scala.sys.error("Non-terminal case should be handled in searchAndReplace: " + unhandled)
  }

}
