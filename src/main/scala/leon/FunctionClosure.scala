package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

object FunctionClosure extends Pass {

  val description = "Closing function with its scoping variables"

  private var enclosingPreconditions: List[Expr] = Nil

  private var pathConstraints: List[Expr] = Nil
  private var newFunDefs: Map[FunDef, FunDef] = Map()
  //private var 

  def apply(program: Program): Program = {
    newFunDefs = Map()
    val funDefs = program.definedFunctions
    funDefs.foreach(fd => {
      enclosingPreconditions = fd.precondition.toList
      pathConstraints = fd.precondition.toList
      fd.body = Some(functionClosure(fd.getBody, fd.args.map(_.id).toSet))
    })
    program
  }

  private def functionClosure(expr: Expr, bindedVars: Set[Identifier]): Expr = expr match {
    case l @ LetDef(fd, rest) => {

      val id = fd.id
      val rt = fd.returnType
      val varDecl = fd.args
      val funBody = fd.getBody
      val precondition = fd.precondition
      val postcondition = fd.postcondition

      val bodyVars: Set[Identifier] = variablesOf(funBody) ++ variablesOf(precondition.getOrElse(BooleanLiteral(true)))
      val capturedVars = bodyVars.intersect(bindedVars)// this should be the variable used that are in the scope
      val (constraints, allCapturedVars) = filterConstraints(capturedVars) //all relevant path constraints
      val capturedVarsWithConstraints = allCapturedVars.toSeq

      val freshVars: Map[Identifier, Identifier] = capturedVarsWithConstraints.map(v => (v, FreshIdentifier(v.name).setType(v.getType))).toMap
      val freshVarsExpr: Map[Expr, Expr] = freshVars.map(p => (p._1.toVariable, p._2.toVariable))

      val extraVarDecls = freshVars.map{ case (_, v2) => VarDecl(v2, v2.getType) }
      val newVarDecls = varDecl ++ extraVarDecls
      val newFunId = FreshIdentifier(id.name)
      val newFunDef = new FunDef(newFunId, rt, newVarDecls)

      val freshPrecondition = precondition.map(expr => replace(freshVarsExpr, expr))
      val freshConstraints = constraints.map(expr => replace(freshVarsExpr, expr))
      newFunDef.precondition = freshConstraints match {
        case List() => freshPrecondition
        case precs => Some(And(freshPrecondition.getOrElse(BooleanLiteral(true)) +: precs))
      }
      newFunDef.postcondition = postcondition.map(expr => replace(freshVarsExpr, expr))

      def substFunInvocInDef(expr: Expr): Option[Expr] = expr match {
        case FunctionInvocation(fd, args) if fd.id == id => Some(FunctionInvocation(newFunDef, args ++ extraVarDecls.map(_.id.toVariable)))
        case _ => None
      }
      val freshBody = replace(freshVarsExpr, funBody)
      val oldPathConstraints = pathConstraints
      pathConstraints = (precondition.getOrElse(BooleanLiteral(true)) :: pathConstraints).map(e => replace(freshVarsExpr, e))
      val recBody = functionClosure(freshBody, bindedVars ++ newVarDecls.map(_.id))
      pathConstraints = oldPathConstraints
      val recBody2 = searchAndReplaceDFS(substFunInvocInDef)(recBody)
      newFunDef.body = Some(recBody2)

      def substFunInvocInRest(expr: Expr): Option[Expr] = expr match {
        case FunctionInvocation(fd, args) if fd.id == id => Some(FunctionInvocation(newFunDef, args ++ capturedVarsWithConstraints.map(_.toVariable)))
        case _ => None
      }
      val recRest = functionClosure(rest, bindedVars)
      val recRest2 = searchAndReplaceDFS(substFunInvocInRest)(recRest)
      LetDef(newFunDef, recRest2).setType(l.getType)
    }

    //case fi @ FunctionInvocation(fd, args) => {

    //}
    case l @ Let(i,e,b) => {
      val re = functionClosure(e, bindedVars)
      pathConstraints ::= Equals(Variable(i), re)
      val rb = functionClosure(b, bindedVars + i)
      pathConstraints = pathConstraints.tail
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
    case i @ IfExpr(cond,then,elze) => {
      val rCond = functionClosure(cond, bindedVars)
      pathConstraints ::= rCond
      val rThen = functionClosure(then, bindedVars)
      pathConstraints = pathConstraints.tail
      pathConstraints ::= Not(rCond)
      val rElze = functionClosure(elze, bindedVars)
      pathConstraints = pathConstraints.tail
      IfExpr(rCond, rThen, rElze).setType(i.getType)
    }
    case m @ MatchExpr(scrut,cses) => sys.error("Will see")//MatchExpr(rec(scrut), cses.map(inCase(_))).setType(m.getType).setPosInfo(m)
    case t if t.isInstanceOf[Terminal] => t
    case unhandled => scala.sys.error("Non-terminal case should be handled in searchAndReplace: " + unhandled)
  }

  //filter the list of constraints, only keeping those relevant to the set of variables
  def filterConstraints(vars: Set[Identifier]): (List[Expr], Set[Identifier]) = {
    var allVars = vars
    var newVars: Set[Identifier] = Set()
    var constraints = pathConstraints
    var filteredConstraints: List[Expr] = Nil
    do {
      allVars ++= newVars
      newVars = Set()
      constraints = pathConstraints.filterNot(filteredConstraints.contains(_))
      constraints.foreach(expr => {
        val vs = variablesOf(expr)
        if(!vs.intersect(allVars).isEmpty) {
          filteredConstraints ::= expr
          newVars ++= vs.diff(allVars)
        }
      })
    } while(newVars != Set())
    (filteredConstraints, allVars)
  }

}
