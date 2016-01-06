/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package xlang

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Extractors._
import leon.purescala.Constructors._
import leon.purescala.ExprOps._
import leon.purescala.TypeOps._
import leon.purescala.Types._
import leon.xlang.Expressions._

object ImperativeCodeElimination extends UnitPhase[Program] {

  val name = "Imperative Code Elimination"
  val description = "Transform imperative constructs into purely functional code"

  def apply(ctx: LeonContext, pgm: Program): Unit = {
    for {
      fd <- pgm.definedFunctions
      body <- fd.body
    } {
      val (res, scope, _) = toFunction(body)(State(fd, Set(), Map()))
      fd.body = Some(scope(res))
    }
  }

  /** varsInScope refers to variable declared in the same level scope.
    * Typically, when entering a nested function body, the scope should be
    * reset to empty */
  private case class State(
    parent: FunDef, 
    varsInScope: Set[Identifier],
    funDefsMapping: Map[FunDef, (FunDef, List[Identifier])]
  ) {
    def withVar(i: Identifier) = copy(varsInScope = varsInScope + i)
    def withFunDef(fd: FunDef, nfd: FunDef, ids: List[Identifier]) = 
      copy(funDefsMapping = funDefsMapping + (fd -> (nfd, ids)))
    def withFunDefs(fdNfd: Seq[(FunDef, (FunDef, List[Identifier]))]) = 
      copy(funDefsMapping = funDefsMapping ++ fdNfd)
  }

  /** Returns a "scope" consisting of purely functional code that defines potentially needed 
    * new variables (val, not var) and a mapping for each modified variable (var, not val :) )
    * to their new name defined in the scope. The first returned valued is the value of the expression
    * that should be introduced as such in the returned scope (the val already refers to the new names) */
  private def toFunction(expr: Expr)(implicit state: State): (Expr, Expr => Expr, Map[Identifier, Identifier]) = {
    import state._
    expr match {
      case LetVar(id, e, b) =>
        val newId = id.freshen
        val (rhsVal, rhsScope, rhsFun) = toFunction(e)
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)(state.withVar(id))
        val scope = (body: Expr) => rhsScope(Let(newId, rhsVal, replaceNames(rhsFun + (id -> newId), bodyScope(body))).copiedFrom(expr))
        (bodyRes, scope, (rhsFun + (id -> newId)) ++ bodyFun)
 
      case Assignment(id, e) =>
        assert(varsInScope.contains(id))
        val newId = id.freshen
        val (rhsVal, rhsScope, rhsFun) = toFunction(e)
        val scope = (body: Expr) => rhsScope(Let(newId, rhsVal, body).copiedFrom(expr))
        (UnitLiteral(), scope, rhsFun + (id -> newId))

      case ite@IfExpr(cond, tExpr, eExpr) =>
        val (cRes, cScope, cFun) = toFunction(cond)
        val (tRes, tScope, tFun) = toFunction(tExpr)
        val (eRes, eScope, eFun) = toFunction(eExpr)

        val iteRType = leastUpperBound(tRes.getType, eRes.getType).get

        val modifiedVars: Seq[Identifier] = (tFun.keys ++ eFun.keys).toSet.intersect(varsInScope).toSeq
        val resId = FreshIdentifier("res", iteRType)
        val freshIds = modifiedVars.map( _.freshen )
        val iteType = tupleTypeWrap(resId.getType +: freshIds.map(_.getType))

        val thenVal = tupleWrap(tRes +: modifiedVars.map(vId => tFun.getOrElse(vId, vId).toVariable))
        val elseVal = tupleWrap(eRes +: modifiedVars.map(vId => eFun.getOrElse(vId, vId).toVariable))
        val iteExpr = IfExpr(cRes, replaceNames(cFun, tScope(thenVal)), replaceNames(cFun, eScope(elseVal))).copiedFrom(ite)

        val scope = (body: Expr) => {
          val tupleId = FreshIdentifier("t", iteType)
          cScope(Let(tupleId, iteExpr, Let(
            resId,
            tupleSelect(tupleId.toVariable, 1, modifiedVars.nonEmpty),
            freshIds.zipWithIndex.foldLeft(body)((b, id) =>
              Let(id._1, tupleSelect(tupleId.toVariable, id._2 + 2, true), b)
            ))
          ).copiedFrom(expr))
        }

        (resId.toVariable, scope, cFun ++ modifiedVars.zip(freshIds).toMap)

      case m @ MatchExpr(scrut, cses) =>
        val csesRhs = cses.map(_.rhs) //we can ignore pattern, and the guard is required to be pure
        val (csesRes, csesScope, csesFun) = csesRhs.map(toFunction).unzip3
        val (scrutRes, scrutScope, scrutFun) = toFunction(scrut)

        val modifiedVars: Seq[Identifier] = csesFun.toSet.flatMap((m: Map[Identifier, Identifier]) => m.keys).intersect(varsInScope).toSeq
        val resId = FreshIdentifier("res", m.getType)
        val freshIds = modifiedVars.map(id => FreshIdentifier(id.name, id.getType))
        val matchType = tupleTypeWrap(resId.getType +: freshIds.map(_.getType))

        val csesVals = csesRes.zip(csesFun).map {
          case (cRes, cFun) => tupleWrap(cRes +: modifiedVars.map(vId => cFun.getOrElse(vId, vId).toVariable))
        }

        val newRhs = csesVals.zip(csesScope).map {
          case (cVal, cScope) => replaceNames(scrutFun, cScope(cVal))
        }
        val matchE = matchExpr(scrutRes, cses.zip(newRhs).map {
          case (mc @ MatchCase(pat, guard, _), newRhs) =>
            MatchCase(pat, guard map { replaceNames(scrutFun, _) }, newRhs).setPos(mc)
        }).setPos(m)

        val scope = (body: Expr) => {
          val tupleId = FreshIdentifier("t", matchType)
          scrutScope(
            Let(tupleId, matchE,
              Let(resId, tupleSelect(tupleId.toVariable, 1, freshIds.nonEmpty),
                freshIds.zipWithIndex.foldLeft(body)((b, id) =>
                  Let(id._1, tupleSelect(tupleId.toVariable, id._2 + 2, true), b)
                )
              )
            )
          )
        }

        (resId.toVariable, scope, scrutFun ++ modifiedVars.zip(freshIds).toMap)
 
      case wh@While(cond, body) =>
        val whileFunDef = new FunDef(parent.id.freshen, Nil, Nil, UnitType).setPos(wh)
        whileFunDef.addFlag(IsLoop(parent))
        whileFunDef.body = Some(
          IfExpr(cond, 
                 Block(Seq(body), FunctionInvocation(whileFunDef.typed, Seq()).setPos(wh)),
                 UnitLiteral()))
        whileFunDef.precondition = wh.invariant
        whileFunDef.postcondition = Some(
          Lambda(
            Seq(ValDef(FreshIdentifier("bodyRes", UnitType))),
            and(Not(getFunctionalResult(cond)), wh.invariant.getOrElse(BooleanLiteral(true))).setPos(wh)
          ).setPos(wh)
        )

        val newExpr = LetDef(List(whileFunDef), FunctionInvocation(whileFunDef.typed, Seq()).setPos(wh)).setPos(wh)
        toFunction(newExpr)

      case Block(Seq(), expr) =>
        toFunction(expr)

      case Block(exprs, expr) =>
        val (scope, fun) = exprs.foldRight((body: Expr) => body, Map[Identifier, Identifier]())((e, acc) => {
          val (accScope, accFun) = acc
          val (_, rScope, rFun) = toFunction(e)
          val scope = (body: Expr) => {
            val withoutPrec = rScope(replaceNames(rFun, accScope(body)))
            e match {
              case FunctionInvocation(tfd, args) if tfd.hasPrecondition =>
                Assert(tfd.withParamSubst(args, tfd.precondition.get), Some("Precondition failed"), withoutPrec)
              case _ =>
                withoutPrec
            }

          }
          (scope, rFun ++ accFun)
        })
        val (lastRes, lastScope, lastFun) = toFunction(expr)
        val finalFun = fun ++ lastFun
        (
          replaceNames(finalFun, lastRes),
          (body: Expr) => scope(replaceNames(fun, lastScope(body))),
          finalFun
        )

      //pure expression (that could still contain side effects as a subexpression) (evaluation order is from left to right)
      case Let(id, e, b) =>
        val (bindRes, bindScope, bindFun) = toFunction(e)
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)
        (
          bodyRes, 
          (b2: Expr) => bindScope(Let(id, bindRes, replaceNames(bindFun, bodyScope(b2))).copiedFrom(expr)), 
          bindFun ++ bodyFun
        )

      //a function invocation can update variables in scope.
      case fi@FunctionInvocation(tfd, args) =>


        val (recArgs, argScope, argFun) = args.foldRight((Seq[Expr](), (body: Expr) => body, Map[Identifier, Identifier]()))((arg, acc) => {
          val (accArgs, accScope, accFun) = acc
          val (argVal, argScope, argFun) = toFunction(arg)
          val newScope = (body: Expr) => argScope(replaceNames(argFun, accScope(body)))
          (argVal +: accArgs, newScope, argFun ++ accFun)
        })

        val fd = tfd.fd
        state.funDefsMapping.get(fd) match { 
          case Some((newFd, modifiedVars)) => {
            val newInvoc = FunctionInvocation(newFd.typed, recArgs ++ modifiedVars.map(id => id.toVariable)).setPos(fi)
            val freshNames = modifiedVars.map(id => id.freshen)
            val tmpTuple = FreshIdentifier("t", newFd.returnType)

            val scope = (body: Expr) => {
              argScope(Let(tmpTuple, newInvoc,
                freshNames.zipWithIndex.foldRight(body)((p, b) =>
                  Let(p._1, TupleSelect(tmpTuple.toVariable, p._2 + 2), b))
              ))
            }
            val newMap = argFun ++ modifiedVars.zip(freshNames).toMap

            (TupleSelect(tmpTuple.toVariable, 1), scope, newMap)
          }
          case None => 
            (FunctionInvocation(tfd, recArgs).copiedFrom(fi), argScope, argFun)
        }


      case LetDef(fds, b) =>
        def fdsWithoutSideEffects =  {
          for(fd <- fds) {
            fd.body.foreach { bd =>
              val (fdRes, fdScope, _) = toFunction(bd)
              fd.body = Some(fdScope(fdRes))
            }
          }
          val (bodyRes, bodyScope, bodyFun) = toFunction(b)
          (bodyRes, (b2: Expr) => LetDef(fds, bodyScope(b2)).setPos(fds.head).copiedFrom(expr), bodyFun)
        }
        if(fds.forall(_.body.isEmpty)) fdsWithoutSideEffects
        else {
          val modified_vars: Seq[(FunDef, List[Identifier])] = for(fd <- fds; bd <- fd.body) yield {
            val modifiedVars: List[Identifier] =
              collect[Identifier]({
                case Assignment(v, _) => Set(v)
                case FunctionInvocation(tfd, _) => state.funDefsMapping.get(tfd.fd).map(p => p._2.toSet).getOrElse(Set())
                case _ => Set()
              })(bd).intersect(state.varsInScope).toList
            (fd, modifiedVars)
          }
          if(modified_vars.forall(_._2.isEmpty)) fdsWithoutSideEffects else {
            val freshNames: Seq[(FunDef, Seq[Identifier])] = modified_vars.map(fdmv => (fdmv._1, fdmv._2.map(id => id.freshen)))
            
            val newParams: Seq[(FunDef, Seq[ValDef])] = freshNames.map(fdfn => (fdfn._1, fdfn._1.params ++ fdfn._2.map(n => ValDef(n))))
            
            val freshVarDecls: Seq[(FunDef, List[Identifier])] = freshNames.map(id => (id._1, id._2.map(_.freshen).toList))
            
            val rewritingMap: Map[Identifier, Identifier] =
                (modified_vars.zip(freshVarDecls).map{
              case ((fd, md), (_, fv)) => (fd, md.zip(fv).toMap)
            }).map(_._2).foldLeft(Map[Identifier, Identifier]())(_ ++ _)
            
            //TODO:
            
            val freshBody: Seq[Option[Expr]] = for(fd <- fds) yield {
              fd.body.map(bd => 
              preMap({
                case Assignment(v, e) => rewritingMap.get(v).map(nv => Assignment(nv, e))
                case Variable(id) => rewritingMap.get(id).map(nid => Variable(nid))
                case _ => None
              })(bd))
            }
            
            val wrappedBody = freshBody.zip(freshNames).zip(freshVarDecls).map{
              case ((freshBodyOpt, (_, freshNames)), (_, freshVarDecls)) =>
                freshBodyOpt.map(freshBody => freshNames.zip(freshVarDecls).foldLeft(freshBody)((body, p) => {
              LetVar(p._2, Variable(p._1), body)
            }))}

            val newReturnType = for((fd, modifiedVars) <- modified_vars)
              yield TupleType(fd.returnType :: modifiedVars.map(_.getType))

            val newFds = for(((fd, newParams), newReturnType) <- newParams.zip(newReturnType))
              yield {
                val newFd = new FunDef(fd.id.freshen, fd.tparams, newParams, newReturnType).setPos(fd)
                newFd.addFlags(fd.flags)
                (fd, newFd)
              }
              
            val mappingToAdd: Seq[(FunDef, (FunDef, List[Identifier]))] =
              for(((fd, newFd), (_, freshVarDecls)) <- newFds.zip(freshVarDecls)) yield (fd -> ((newFd, freshVarDecls.toList)))

            //Seq[Option[(fdRes, fdScope, fdFun)]] = 
            val fdsResScopeFun = for(wrappedBodyOpt <- wrappedBody) yield {
              wrappedBodyOpt.map(wrappedBody => 
                toFunction(wrappedBody)(
                  State(state.parent, Set(), 
                        state.funDefsMapping.map{
  case (fd, (nfd, mvs)) =>
  (fd, (nfd, mvs.map(v => rewritingMap.getOrElse(v, v))))} ++ mappingToAdd)
                )
              )
            }
            
            val newRes= for((optFdsResScopeFun, (_, freshVarDecls)) <- fdsResScopeFun.zip(freshVarDecls)) yield {
              for((fdRes, fdScope, fdFun) <- optFdsResScopeFun) yield {
                Tuple(fdRes :: freshVarDecls.map(vd => fdFun(vd).toVariable))
              }
            }
            val newbody = for((optFdsResScopeFun, newRes) <- fdsResScopeFun.zip(newRes)) yield {
              for(newRes <- newRes;
                  (fdRes, fdScope, fdFun) <- optFdsResScopeFun) yield {
                fdScope(newRes)
              }
            }
            val fdForState = for(((((fd, newFd), optNewbody), (_, modifiedVars)), (_, freshNames))
                <- newFds.zip(newbody).zip(modified_vars).zip(freshNames)) yield {
              newFd.body = optNewbody
              newFd.precondition = fd.precondition.map(prec => {
                replace(modifiedVars.zip(freshNames).map(p => (p._1.toVariable, p._2.toVariable)).toMap, prec)
              })
              newFd.postcondition = fd.postcondition.map(post => {
                val Lambda(Seq(res), postBody) = post
                val newRes = ValDef(FreshIdentifier(res.id.name, newFd.returnType))

                val newBody =
                  replace(
                    modifiedVars.zipWithIndex.map{ case (v, i) => 
                      (v.toVariable, TupleSelect(newRes.toVariable, i+2)): (Expr, Expr)}.toMap ++
                    modifiedVars.zip(freshNames).map{ case (ov, nv) => 
                      (Old(ov), nv.toVariable)}.toMap +
                    (res.toVariable -> TupleSelect(newRes.toVariable, 1)),
                  postBody)
                Lambda(Seq(newRes), newBody).setPos(post)
              })
              (fd, (newFd, modifiedVars))
            }
            val (bodyRes, bodyScope, bodyFun) = toFunction(b)(state.withFunDefs(fdForState))
            (bodyRes, (b2: Expr) => LetDef(newFds.map(_._1), bodyScope(b2)).copiedFrom(expr), bodyFun)
          }
        }

      case c @ Choose(b) =>
        //Recall that Choose cannot mutate variables from the scope
        (c, (b2: Expr) => b2, Map())

      case And(args) =>
        val ifExpr = args.reduceRight((el, acc) => IfExpr(el, acc, BooleanLiteral(false)))
        toFunction(ifExpr)

      case Or(args) =>
        val ifExpr = args.reduceRight((el, acc) => IfExpr(el, BooleanLiteral(true), acc))
        toFunction(ifExpr)

      case n @ Operator(args, recons) =>
        val (recArgs, scope, fun) = args.foldRight((Seq[Expr](), (body: Expr) => body, Map[Identifier, Identifier]()))((arg, acc) => {
          val (accArgs, accScope, accFun) = acc
          val (argVal, argScope, argFun) = toFunction(arg)
          val newScope = (body: Expr) => argScope(replaceNames(argFun, accScope(body)))
          (argVal +: accArgs, newScope, argFun ++ accFun)
        })
        (recons(recArgs).copiedFrom(n), scope, fun)

      case _ =>
        sys.error("not supported: " + expr)
    }
  }

  def replaceNames(fun: Map[Identifier, Identifier], expr: Expr) = replaceFromIDs(fun mapValues Variable, expr)

  
  /* Extract functional result value. Useful to remove side effect from conditions when moving it to post-condition */
  private def getFunctionalResult(expr: Expr): Expr = {
    preMap({
      case Block(_, res) => Some(res)
      case _ => None
    })(expr)
  }

}
