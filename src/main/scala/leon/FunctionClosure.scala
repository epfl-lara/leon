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

      def introduceLets(expr: Expr, fd2FreshFd: Map[FunDef, (FunDef, Seq[Variable])]): Expr = {
        val (newExpr, _) = enclosingLets.foldLeft((expr, Map[Identifier, Identifier]()))((acc, p) => {
          val newId = FreshIdentifier(p._1.name).setType(p._1.getType)
          val newMap = acc._2 + (p._1 -> newId)
          val newBody = functionClosure(acc._1, newBindedVars, freshIds ++ newMap, fd2FreshFd)
          (Let(newId, p._2, newBody), newMap)
        })
        functionClosure(newExpr, newBindedVars, freshIds, fd2FreshFd)
      }


      val newPrecondition = simplifyLets(introduceLets(And((capturedConstraints ++ fd.precondition).toSeq), fd2FreshFd))
      newFunDef.precondition = if(newPrecondition == BooleanLiteral(true)) None else Some(newPrecondition)

      val freshPostcondition = fd.postcondition.map(post => introduceLets(post, fd2FreshFd))
      newFunDef.postcondition = freshPostcondition
      
      pathConstraints = fd.precondition.getOrElse(BooleanLiteral(true)) :: pathConstraints
      //val freshBody = fd.body.map(body => introduceLets(body, fd2FreshFd + (fd -> ((newFunDef, extraVarDeclFreshIds.map(_.toVariable))))))
      val freshBody = fd.body.map(body => introduceLets(body, fd2FreshFd + (fd -> ((newFunDef, extraVarDeclOldIds.map(_.toVariable))))))
      newFunDef.body = freshBody
      pathConstraints = pathConstraints.tail

      //val freshRest = functionClosure(rest, bindedVars, id2freshId, fd2FreshFd + (fd -> 
      //                  ((newFunDef, extraVarDeclOldIds.map(id => id2freshId.get(id).getOrElse(id).toVariable)))))
      val freshRest = functionClosure(rest, bindedVars, id2freshId, fd2FreshFd + (fd -> ((newFunDef, extraVarDeclOldIds.map(_.toVariable)))))
      freshRest.setType(l.getType)
    }
    case l @ Let(i,e,b) => {
      val re = functionClosure(e, bindedVars, id2freshId, fd2FreshFd)
      //we need the enclosing lets to always refer to the original ids, because it might be expand later in a highly nested function
      enclosingLets ::= (i, replace(id2freshId.map(p => (p._2.toVariable, p._1.toVariable)), re)) 
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
        FunctionInvocation(nfd, args.map(arg => functionClosure(arg, bindedVars, id2freshId, fd2FreshFd)) ++ 
                                extraArgs.map(v => replace(id2freshId.map(p => (p._1.toVariable, p._2.toVariable)), v))).setPosInfo(fi)
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
    case m @ MatchExpr(scrut,cses) => {
      val scrutRec = functionClosure(scrut, bindedVars, id2freshId, fd2FreshFd)
      val csesRec = cses.map{
        case SimpleCase(pat, rhs) => {
          val binders = pat.binders
          val cond = conditionForPattern(scrut, pat)
          pathConstraints ::= cond
          val rRhs = functionClosure(rhs, bindedVars ++ binders, id2freshId, fd2FreshFd)
          pathConstraints = pathConstraints.tail
          SimpleCase(pat, rRhs)
        }
        case GuardedCase(pat, guard, rhs) => {
          val binders = pat.binders
          val cond = conditionForPattern(scrut, pat)
          pathConstraints ::= cond
          val rRhs = functionClosure(rhs, bindedVars ++ binders, id2freshId, fd2FreshFd)
          val rGuard = functionClosure(guard, bindedVars ++ binders, id2freshId, fd2FreshFd)
          pathConstraints = pathConstraints.tail
          GuardedCase(pat, rGuard, rRhs)
        }
      }
      val tpe = csesRec.head.rhs.getType
      MatchExpr(scrutRec, csesRec).setType(tpe).setPosInfo(m)
    }
    case v @ Variable(id) => id2freshId.get(id) match {
      case None => v
      case Some(nid) => Variable(nid)
    }
    case t if t.isInstanceOf[Terminal] => t
    case unhandled => scala.sys.error("Non-terminal case should be handled in FunctionClosure: " + unhandled)
  }

  def freshIdInPat(pat: Pattern, id2freshId: Map[Identifier, Identifier]): Pattern = pat match {
    case InstanceOfPattern(binder, classTypeDef) => InstanceOfPattern(binder.map(id2freshId(_)), classTypeDef)
    case WildcardPattern(binder) => WildcardPattern(binder.map(id2freshId(_)))
    case CaseClassPattern(binder, caseClassDef, subPatterns) => CaseClassPattern(binder.map(id2freshId(_)), caseClassDef, subPatterns.map(freshIdInPat(_, id2freshId)))
    case TuplePattern(binder, subPatterns) => TuplePattern(binder.map(id2freshId(_)), subPatterns.map(freshIdInPat(_, id2freshId)))
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
