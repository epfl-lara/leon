package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

object FunctionClosure extends Pass {

  val description = "Closing function with its scoping variables"

  private var enclosingPreconditions: List[Expr] = Nil

  def apply(program: Program): Program = {
    val funDefs = program.definedFunctions
    funDefs.foreach(fd => {
      enclosingPreconditions = fd.precondition.toList
      fd.body = Some(functionClosure(fd.getBody, fd.args.map(_.id).toSet))
    })
    program
  }

  private def functionClosure(expr: Expr, bindedVars: Set[Identifier]): Expr = expr match {
    case l @ LetDef(fd@FunDef(id, rt, varDecl, Some(funBody), _, _), rest) => {
      enclosingPreconditions = fd.precondition match {
        case Some(pre) => pre :: enclosingPreconditions
        case None => enclosingPreconditions
      }
      val bodyVars: Set[Identifier] = variablesOf(funBody) 
      val preconditionVars: Set[Identifier] = enclosingPreconditions.foldLeft(Set[Identifier]())((s, pre) => s ++ variablesOf(pre))
      val vars = bodyVars ++ preconditionVars
      val capturedVars = vars.intersect(bindedVars).toSeq // this should be the variable used that are in the scope
      val freshVars: Map[Identifier, Identifier] = capturedVars.map(v => (v, FreshIdentifier(v.name).setType(v.getType))).toMap
      val freshVarsExpr: Map[Expr, Expr] = freshVars.map(p => (p._1.toVariable, p._2.toVariable))
      val freshBody = replace(freshVarsExpr, funBody)
      val extraVarDecls = freshVars.map{ case (_, v2) => VarDecl(v2, v2.getType) }
      val newVarDecls = varDecl ++ extraVarDecls
      val newFunId = FreshIdentifier(id.name)
      val newFunDef = new FunDef(newFunId, rt, newVarDecls)
      newFunDef.precondition = enclosingPreconditions match {
        case List() => None
        case precs => Some(replace(freshVarsExpr, And(precs)))
      }
      newFunDef.postcondition = fd.postcondition.map(expr => replace(freshVarsExpr, expr))
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
      //need to remove the enclosing precondition before considering the rest
      enclosingPreconditions = fd.precondition match {
        case Some(_) => enclosingPreconditions.tail
        case None => enclosingPreconditions
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
