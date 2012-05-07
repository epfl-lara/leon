package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

object FunctionClosure extends Pass {

  val description = "Closing function with its scoping variables"

  private var pathConstraints: List[Expr] = Nil
  private var enclosingLets: List[(Identifier, Expr)] = Nil
  private var newFunDefs: Map[FunDef, FunDef] = Map()
  private var originalsIds: Map[Identifier, Identifier] = Map()
  private var topLevelFuns: Set[FunDef] = Set()

  def apply(program: Program): Program = {
    newFunDefs = Map()
    val funDefs = program.definedFunctions
    funDefs.foreach(fd => {
      pathConstraints = fd.precondition.toList
      fd.body = fd.body.map(b => functionClosure(b, fd.args.map(_.id).toSet, Map(), Map()))
    })
    val Program(id, ObjectDef(objId, defs, invariants)) = program
    Program(id, ObjectDef(objId, defs ++ topLevelFuns, invariants))
  }

  private def functionClosure(expr: Expr, bindedVars: Set[Identifier], id2freshId: Map[Identifier, Identifier], fd2FreshFd: Map[FunDef, (FunDef, Seq[Variable])]): Expr = expr match {
    case l @ LetDef(fd, rest) => {
      val capturedVars: Set[Identifier] = bindedVars.diff(enclosingLets.map(_._1).toSet)
      val capturedConstraints: Set[Expr] = pathConstraints.toSet

      val freshIds: Map[Identifier, Identifier] = capturedVars.map(id => (id, FreshIdentifier(id.name).setType(id.getType))).toMap
      freshIds.foreach(p => originalsIds += (p._2 -> p._1))
      val freshVars: Map[Expr, Expr] = freshIds.map(p => (p._1.toVariable, p._2.toVariable))
      
      val extraVarDeclOldIds: Seq[Identifier] = capturedVars.toSeq
      val extraVarDeclFreshIds: Seq[Identifier] = extraVarDeclOldIds.map(freshIds(_))
      val extraVarDecls: Seq[VarDecl] = extraVarDeclFreshIds.map(id =>  VarDecl(id, id.getType))
      val newVarDecls: Seq[VarDecl] = fd.args ++ extraVarDecls
      val newBindedVars: Set[Identifier] = bindedVars ++ fd.args.map(_.id)
      val newFunId = FreshIdentifier(fd.id.name)

      val newFunDef = new FunDef(newFunId, fd.returnType, newVarDecls).setPosInfo(fd)
      topLevelFuns += newFunDef
      newFunDef.fromLoop = fd.fromLoop
      newFunDef.parent = fd.parent
      newFunDef.addAnnotation(fd.annotations.toSeq:_*)

      val newPrecondition = functionClosure(And((capturedConstraints ++ fd.precondition).toSeq), newBindedVars, freshIds, fd2FreshFd)
      newFunDef.precondition = if(newPrecondition == BooleanLiteral(true)) None else Some(newPrecondition)

      val freshPostcondition = fd.postcondition.map(expr => functionClosure(expr, newBindedVars, freshIds, fd2FreshFd))
      newFunDef.postcondition = freshPostcondition
      
      pathConstraints = fd.precondition.getOrElse(BooleanLiteral(true)) :: pathConstraints
      val freshBody = fd.body.map(expr => 
        functionClosure(expr, newBindedVars, freshIds, fd2FreshFd + (fd -> ((newFunDef, extraVarDeclFreshIds.map(_.toVariable))))))
      pathConstraints = pathConstraints.tail
      newFunDef.body = freshBody

      val freshRest = functionClosure(rest, bindedVars, id2freshId, fd2FreshFd + (fd -> 
                        ((newFunDef, extraVarDeclOldIds.map(id => id2freshId.get(id).getOrElse(id).toVariable)))))
      freshRest.setType(l.getType)
    }
    case l @ Let(i,e,b) => {
      val re = functionClosure(e, bindedVars, id2freshId, fd2FreshFd)
      enclosingLets ::= (i, replace(originalsIds.map(p => (p._1.toVariable, p._2.toVariable)), re))
      //pathConstraints :: Equals(i.toVariable, re)
      val rb = functionClosure(b, bindedVars + i, id2freshId, fd2FreshFd)
      enclosingLets = enclosingLets.tail
      //pathConstraints = pathConstraints.tail
      Let(i, re, rb).setType(l.getType)
    }
    case i @ IfExpr(cond,then,elze) => {
      /*
         when acumulating path constraints, take the condition without closing it first, so this
         might not work well with nested fundef in if then else condition
      */
      val rCond = functionClosure(cond, bindedVars, id2freshId, fd2FreshFd)
      pathConstraints ::= cond//rCond
      val rThen = functionClosure(then, bindedVars, id2freshId, fd2FreshFd)
      pathConstraints = pathConstraints.tail
      pathConstraints ::= Not(cond)//Not(rCond)
      val rElze = functionClosure(elze, bindedVars, id2freshId, fd2FreshFd)
      pathConstraints = pathConstraints.tail
      IfExpr(rCond, rThen, rElze).setType(i.getType)
    }
    case fi @ FunctionInvocation(fd, args) => fd2FreshFd.get(fd) match {
      case None => FunctionInvocation(fd, args.map(arg => functionClosure(arg, bindedVars, id2freshId, fd2FreshFd))).setPosInfo(fi)
      case Some((nfd, extraArgs)) => 
        FunctionInvocation(nfd, args.map(arg => functionClosure(arg, bindedVars, id2freshId, fd2FreshFd)) ++ extraArgs).setPosInfo(fi)
    }
    case n @ NAryOperator(args, recons) => {
      val rargs = args.map(a => functionClosure(a, bindedVars, id2freshId, fd2FreshFd))
      recons(rargs).setType(n.getType)
    }
    case b @ BinaryOperator(t1,t2,recons) => {
      val r1 = functionClosure(t1, bindedVars, id2freshId, fd2FreshFd)
      val r2 = functionClosure(t2, bindedVars, id2freshId, fd2FreshFd)
      recons(r1,r2).setType(b.getType)
    }
    case u @ UnaryOperator(t,recons) => {
      val r = functionClosure(t, bindedVars, id2freshId, fd2FreshFd)
      recons(r).setType(u.getType)
    }
    case m @ MatchExpr(scrut,cses) => { //TODO: will not work if there are actual nested function in cases
      //val rScrut = functionClosure(scrut, bindedVars, id2freshId, fd2FreshFd)
      m
    }
    case v @ Variable(id) => id2freshId.get(id) match {
      case None => replace(
                     id2freshId.map(p => (p._1.toVariable, p._2.toVariable)),
                     enclosingLets.foldLeft(v: Expr){ 
                       case (expr, (id, value)) => replace(Map(id.toVariable -> value), expr) 
                     })
      case Some(nid) => Variable(nid)
    }
    case t if t.isInstanceOf[Terminal] => t
    case unhandled => scala.sys.error("Non-terminal case should be handled in FunctionClosure: " + unhandled)
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
