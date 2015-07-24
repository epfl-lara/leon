/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Extractors._
import ExprOps._
import Constructors._

class FunctionClosure extends TransformationPhase {

  val name = "Function Closure"
  val description = "Closing function with its scoping variables"

  // TODO: Rewrite this phase
  /* I know, that's a lot of mutable variables */
  private var pathConstraints: List[Expr] = Nil
  private var enclosingLets: List[(Identifier, Expr)] = Nil
  private var newFunDefs: Map[FunDef, FunDef] = Map()
  private var topLevelFuns: Set[FunDef] = Set()
  private var parent: FunDef = null //refers to the current toplevel parent

  def apply(ctx: LeonContext, program: Program): Program = {

    val newUnits = program.units.map { u => u.copy(defs = u.defs map { 
      case m: ModuleDef =>
        pathConstraints = Nil
        enclosingLets  = Nil
        newFunDefs  = Map()
        topLevelFuns = Set()
        parent = null

        val funDefs = m.definedFunctions
        funDefs.foreach(fd => {
          parent = fd
          pathConstraints = fd.precondition.toList
          fd.body = fd.body.map(b => functionClosure(b, fd.params.map(_.id).toSet, Map(), Map()))
        })

        ModuleDef(m.id, m.defs ++ topLevelFuns, m.isPackageObject )
      case cd => cd
    })}
    Program(newUnits)
  }

  private def functionClosure(expr: Expr, bindedVars: Set[Identifier], id2freshId: Map[Identifier, Identifier], fd2FreshFd: Map[FunDef, (FunDef, Seq[Variable])]): Expr = expr match {
    case l @ LetDef(fd, rest) => {
      val capturedVars: Set[Identifier] = bindedVars.diff(enclosingLets.map(_._1).toSet)
      val capturedConstraints: Set[Expr] = pathConstraints.toSet

      val freshIds: Map[Identifier, Identifier] = capturedVars.map(id => (id, id.freshen)).toMap

      val extraValDefOldIds: Seq[Identifier] = capturedVars.toSeq
      val extraValDefFreshIds: Seq[Identifier] = extraValDefOldIds.map(freshIds(_))
      val extraValDefs: Seq[ValDef] = extraValDefFreshIds.map(ValDef(_))
      val newValDefs: Seq[ValDef] = fd.params ++ extraValDefs
      val newBindedVars: Set[Identifier] = bindedVars ++ fd.params.map(_.id)
      val newFunId = FreshIdentifier(fd.id.name, alwaysShowUniqueID = true) //since we hoist this at the top level, we need to make it a unique name

      val newFunDef = new FunDef(newFunId, fd.tparams, fd.returnType, newValDefs).copiedFrom(fd)
      topLevelFuns += newFunDef
      newFunDef.copyContentFrom(fd) //TODO: this still has some dangerous side effects (?)

      def introduceLets(expr: Expr, fd2FreshFd: Map[FunDef, (FunDef, Seq[Variable])]): Expr = {
        val (newExpr, _) = enclosingLets.foldLeft((expr, Map[Identifier, Identifier]()))((acc, p) => {
          val newId = p._1.freshen
          val newMap = acc._2 + (p._1 -> newId)
          val newBody = functionClosure(acc._1, newBindedVars, freshIds ++ newMap, fd2FreshFd)
          (Let(newId, p._2, newBody), newMap)
        })
        functionClosure(newExpr, newBindedVars, freshIds, fd2FreshFd)
      }

      val newPrecondition = simplifyLets(introduceLets(and((capturedConstraints ++ fd.precondition).toSeq :_*), fd2FreshFd))
      newFunDef.precondition = if(newPrecondition == BooleanLiteral(true)) None else Some(newPrecondition)

      val freshPostcondition = fd.postcondition.map { case post @ Lambda(args, body) =>
        Lambda(args, introduceLets(body, fd2FreshFd).setPos(body)).setPos(post)
      }
      newFunDef.postcondition = freshPostcondition
      
      pathConstraints = fd.precondition.getOrElse(BooleanLiteral(true)) :: pathConstraints
      val freshBody = fd.body.map(body => introduceLets(body, fd2FreshFd + (fd -> ((newFunDef, extraValDefOldIds.map(_.toVariable))))))
      newFunDef.body = freshBody
      pathConstraints = pathConstraints.tail

      val freshRest = functionClosure(rest, bindedVars, id2freshId, fd2FreshFd + (fd -> ((newFunDef, extraValDefOldIds.map(_.toVariable)))))
      freshRest.copiedFrom(l)
    }
    case l @ Let(i,e,b) => {
      val re = functionClosure(e, bindedVars, id2freshId, fd2FreshFd)
      //we need the enclosing lets to always refer to the original ids, because it might be expand later in a highly nested function
      enclosingLets ::= (i, replace(id2freshId.map(p => (p._2.toVariable, p._1.toVariable)), re)) 
      //pathConstraints :: Equals(i.toVariable, re)
      val rb = functionClosure(b, bindedVars + i, id2freshId, fd2FreshFd)
      enclosingLets = enclosingLets.tail
      //pathConstraints = pathConstraints.tail
      Let(i, re, rb).copiedFrom(l)
    }
    case i @ IfExpr(cond,thenn,elze) => {
      /*
         when acumulating path constraints, take the condition without closing it first, so this
         might not work well with nested fundef in if then else condition
      */
      val rCond = functionClosure(cond, bindedVars, id2freshId, fd2FreshFd)
      pathConstraints ::= cond//rCond
      val rThen = functionClosure(thenn, bindedVars, id2freshId, fd2FreshFd)
      pathConstraints = pathConstraints.tail
      pathConstraints ::= Not(cond)//Not(rCond)
      val rElze = functionClosure(elze, bindedVars, id2freshId, fd2FreshFd)
      pathConstraints = pathConstraints.tail
      IfExpr(rCond, rThen, rElze).copiedFrom(i)
    }
    case fi @ FunctionInvocation(tfd, args) => fd2FreshFd.get(tfd.fd) match {
      case None =>
        FunctionInvocation(tfd,
                           args.map(arg => functionClosure(arg, bindedVars, id2freshId, fd2FreshFd))).copiedFrom(fi)
      case Some((nfd, extraArgs)) => 
        FunctionInvocation(nfd.typed(tfd.tps),
                           args.map(arg => functionClosure(arg, bindedVars, id2freshId, fd2FreshFd)) ++ 
                           extraArgs.map(v => replace(id2freshId.map(p => (p._1.toVariable, p._2.toVariable)), v))).copiedFrom(fi)
    }
    case m @ MatchExpr(scrut,cses) => {
      val scrutRec = functionClosure(scrut, bindedVars, id2freshId, fd2FreshFd)
      val csesRec = cses.map{ cse =>
        import cse._
        val binders = pattern.binders
        val cond = conditionForPattern(scrut, pattern)
        pathConstraints ::= cond
        val rRhs = functionClosure(rhs, bindedVars ++ binders, id2freshId, fd2FreshFd)
        val rGuard = optGuard map { functionClosure(_, bindedVars ++ binders, id2freshId, fd2FreshFd) }
        pathConstraints = pathConstraints.tail
        MatchCase(pattern, rGuard, rRhs)
      }
      matchExpr(scrutRec, csesRec).copiedFrom(m)
    }
    case v @ Variable(id) => id2freshId.get(id) match {
      case None => v
      case Some(nid) => Variable(nid)
    }
    case n @ Operator(args, recons) => {
      val rargs = args.map(a => functionClosure(a, bindedVars, id2freshId, fd2FreshFd))
      recons(rargs).copiedFrom(n)
    }
    case unhandled => scala.sys.error("Non-terminal case should be handled in FunctionClosure: " + unhandled)
  }

  def freshIdInPat(pat: Pattern, id2freshId: Map[Identifier, Identifier]): Pattern = pat match {
    case InstanceOfPattern(binder, classTypeDef) => InstanceOfPattern(binder.map(id2freshId(_)), classTypeDef)
    case WildcardPattern(binder) => WildcardPattern(binder.map(id2freshId(_)))
    case CaseClassPattern(binder, caseClassDef, subPatterns) => CaseClassPattern(binder.map(id2freshId(_)), caseClassDef, subPatterns.map(freshIdInPat(_, id2freshId)))
    case TuplePattern(binder, subPatterns) => TuplePattern(binder.map(id2freshId(_)), subPatterns.map(freshIdInPat(_, id2freshId)))
    case UnapplyPattern(binder, fd, subPatterns) => UnapplyPattern(binder.map(id2freshId(_)), fd, subPatterns.map(freshIdInPat(_, id2freshId)))
    case LiteralPattern(binder, lit) => LiteralPattern(binder.map(id2freshId(_)), lit)
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
        if(vs.intersect(allVars).nonEmpty) {
          filteredConstraints ::= expr
          newVars ++= vs.diff(allVars)
        }
      })
    } while(newVars != Set())
    (filteredConstraints, allVars)
  }
}
