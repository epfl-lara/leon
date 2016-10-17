package leon
package laziness

import invariant.util._
import invariant.structure.FunctionUtils._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import transformations._
import leon.invariant.util.TypeUtil._
import HOMemUtil._
import ProgramUtil._
import PredicateUtil._
import purescala.TypeOps.bestRealType
import LetTupleSimplification._

/**
 * TODO: check argument preconditions of closure (they can be made preconditions of the eval function w.r.t appropriate match conditions)
 * (a) add state to every function in the program
 * (b) thread state through every expression in the program sequentially
 * (c) replace lambda constructions with case class creations
 * (d) replace cached with currentState.contains()
 * (e) replace indirect calls to dispatch with current state
 */
class ClosureConverter(p: Program, ctx: LeonContext,
                       closureFactory: ClosureFactory,
                       funsManager: FunctionsManager) {
  import closureFactory._
  val debug = false
  // flags
  //val removeRecursionViaEval = false
  val refEq = ctx.findOptionOrDefault(HOInferencePhase.optRefEquality)

  val funsNeedStates = funsManager.funsNeedStates
  val funsRetStates = funsManager.funsRetStates
  val funsNeedStateTps = funsManager.funsNeedStateTps
  val closureTnames = closureTypeNames

  //println("Functions needing state: "+funsNeedStates.map(_.id))
  /**
   * Copies a identifier if it is not of the required type.
   * Note this method has side-effects
   */
  var idmap = Map[Identifier, Identifier]()
  def makeIdOfType(oldId: Identifier, tpe: TypeTree): Identifier = {
    if (oldId.getType != tpe) {
      val freshid = FreshIdentifier(oldId.name, tpe, true)
      idmap += (oldId -> freshid)
      freshid
    } else oldId
  }

  val funMap = ProgramUtil.userLevelFunctions(p).map { fd =>
    val stparams =
      if (funsNeedStateTps(fd)) {
        // create fresh type parameters for the state
        stateTParams.map(_ => TypeParameter.fresh("P@"))
      } else Seq()
    // (a) replace closure types, memoFunTypes in parameters and return values
    val nparams = fd.params map {
      case ValDef(id) if isFunSetType(id.getType) => // replace this with set of memoAbs
        ValDef(makeIdOfType(id, stateType(stparams)))
      case vd =>
        ValDef(makeIdOfType(vd.id, replaceClosureTypes(vd.getType)))
    }
    val nretType = replaceClosureTypes(fd.returnType)

    val nfd = if (funsNeedStates(fd)) {
      val stType = stateType(stparams)
      val stParam = ValDef(FreshIdentifier("st@", stType))
      val retTypeWithState =
        if (funsRetStates(fd))
          TupleType(Seq(nretType, stType))
        else
          nretType
      // the type parameters will be unified later
      new FunDef(FreshIdentifier(fd.id.name), fd.tparams ++ (stparams map TypeParameterDef),
        nparams :+ stParam, retTypeWithState)
      // body of these functions are defined later
    } else if (funsNeedStateTps(fd)) {
      new FunDef(FreshIdentifier(fd.id.name), fd.tparams ++ (stparams map TypeParameterDef), nparams, nretType)
    } else {
      new FunDef(FreshIdentifier(fd.id.name), fd.tparams, nparams, nretType)
    }
    // copy annotations
    fd.flags.foreach(nfd.addFlag(_))
    (fd -> nfd)
  }.toMap

  //TODO: Optimization: we can omit some functions whose translations will not be recursive.
  def takesStateButIndep(fd: FunDef) =
    funsNeedStates(fd) && funsManager.hasStateIndependentBehavior(fd)

  /**
   * A set of uninterpreted functions that are used
   * in specs to ensure that value part is independent of the state
   */
  val uiFuncs: Map[FunDef, (FunDef, Option[FunDef])] = funMap.collect {
    case (old, newf) if takesStateButIndep(old) =>
      val params = newf.params.take(old.params.size) // ignore the state params
      val retType =
        if (funsRetStates(old)) {
          val TupleType(valtype +: _) = newf.returnType
          valtype
        } else newf.returnType
      val ufd = new FunDef(FreshIdentifier(newf.id.name + "UI"), old.tparams, params, retType)

      // we also need to create a function that assumes that the result equals
      // the uninterpreted function
      val valres = ValDef(FreshIdentifier("valres", retType))
      val pred = new FunDef(FreshIdentifier(newf.id.name + "ValPred"), old.tparams,
        params :+ valres, BooleanType)
      val resid = FreshIdentifier("res", pred.returnType)
      pred.fullBody = Ensuring(
        Equals(valres.id.toVariable,
          FunctionInvocation(TypedFunDef(ufd, old.tparams.map(_.tp)), params.map(_.id.toVariable))), // res = funUI(..)
        Lambda(Seq(ValDef(resid)), resid.toVariable)) // holds
      pred.addFlag(Annotation("axiom", Seq())) // @axiom is similar to @library
      (old -> (ufd, Some(pred)))

    case (old, newf) if isMemoized(old) =>
      // here 'newf' cannot for sure take state params, otherwise it must be state indep
      if (funsNeedStates(old))
        throw new IllegalStateException("Memoized Operation that has a state dependent behavior: " + old)
      else {
        val ufd = new FunDef(FreshIdentifier(newf.id.name + "UI"), newf.tparams, newf.params, newf.returnType)
        (old -> (ufd, None))
      }
  }.toMap

  /**
   * A set of uninterpreted functions that return fixed but uninterpreted states
   * Note: here I am using mutation on purpose to create uninterpreted states on
   * demand.
   */
  val uninterpretedState = {
    // create a body-less fundef that will return a state
    val stType = stateType()
    new FunDef(FreshIdentifier("uiState"), stateTParams.map(TypeParameterDef), Seq(), stType)
  }

  def uninterpretedStateFor(tparams: Seq[TypeParameter]) = FunctionInvocation(TypedFunDef(uninterpretedState, tparams), Seq())

  /**
   * A set of functions that model unknown targets of closures.
   */
  val unknownTargets = tpeToADT.collect {
    case (tname, (ft @ FunctionType(argTps, retTp), _, _, Some(cdef))) =>
      // create fresh type parameters for the state
      val stTparams = stateTParams.map(_ => TypeParameter.fresh("P@"))
      val stType = stateType(stTparams)
      val params = argTps.zipWithIndex.map {
        case (tp, i) =>
          ValDef(FreshIdentifier("a" + i, replaceClosureTypes(tp)))
      } :+ ValDef(FreshIdentifier("st", stType))
      val retTypeWithState = TupleType(Seq(replaceClosureTypes(retTp), stType))
      // the type parameters will be unified later
      val nfd = new FunDef(FreshIdentifier("u" + tname),
        (getTypeParameters(ft) ++ stTparams) map TypeParameterDef,
        params, retTypeWithState)
      (tname -> nfd)
  }.toMap

  /**
   * Create dispatch functions for each closure type.
   * Note: the dispatch functions will be annotated as library so that
   * their pre/posts are not checked (the fact that they hold are verified separately)
   * Also by using 'assume-pre' we can also assume the preconditions of closures at
   * the call-sites.
   */
  val evalFunctions = closureTnames.map { tname =>
    functionType(tname) match {
      case ft @ FunctionType(argTps, retTp) =>
        val absdef = absClosure(tname)
        val cdefs = concreteClosures(tname)
        // construct parameters and return types
        val recvTparams = getTypeParameters(ft)
        val recv = FreshIdentifier("cl", AbstractClassType(absdef, recvTparams))
        val stTparams = stateTParams.map(_ => TypeParameter.fresh("P@"))
        val stType = stateType(stTparams)
        val stParam = FreshIdentifier("st@", stType)
        val otherParams = argTps.zipWithIndex.map {
          case (tp, i) =>
            FreshIdentifier("a" + i, replaceClosureTypes(tp))
        }
        val withStTparams = recvTparams ++ stTparams
        // TODO: need to handle preconditions on arguments!!
        // create body of the eval fucntion
        // create a match case to switch over the possible class defs and invoke the corresponding functions
        val bodyMatchCases = cdefs map { cdef =>
          val ctype = CaseClassType(cdef, recvTparams) // we know that the type parameters of cdefs are same as absdefs
          val binder = FreshIdentifier("t", ctype)
          val pattern = InstanceOfPattern(Some(binder), ctype)
          // create a body of the match
          val flds = cdef.fields
          /* TODO: code for handling result field
           * cdef.fields.dropRight(1)*/
          def exprForcapturedArg(arg: Identifier) = {
            flds.find(fld => fld.id.name == arg.name) match {
              case Some(fld) => CaseClassSelector(ctype, binder.toVariable, fld.id)
              case _         => throw new IllegalStateException(s"Cannot find field of $ctype for captured arg $arg")
            }
          }
          val srcTarget = targetOfClosure(cdef).get
          val targetFun = funMap(srcTarget)
          // construct arguments of the target
          val targetArgs = lambdaOfClosure(cdef).get match {
            case l @ Lambda(args, FunctionInvocation(TypedFunDef(srcTarget, _), allArgs)) =>
              val argMap = ((args.map(_.id) zip otherParams.map(_.toVariable)) ++ (capturedVars(l).map(a => a -> exprForcapturedArg(a)))).toMap
              allArgs.map {
                case Variable(id) => argMap(id)
              }
          }
          // invoke the target fun with appropriate values
          val invoke =
            if (funsNeedStates(srcTarget)) {
              FunctionInvocation(TypedFunDef(targetFun, withStTparams), targetArgs :+ stParam.toVariable)
            } else
              FunctionInvocation(TypedFunDef(targetFun, recvTparams), targetArgs)
          // construct the return values
          val rhs = if (stateUpdatingTypes(tname)) {
            val invokeRes = FreshIdentifier("dres", invoke.getType, true)
            //println(s"invoking function $targetFun with args $args")
            val (valPart, currState) =
              if (funsRetStates(srcTarget)) {
                (TupleSelect(invokeRes.toVariable, 1), TupleSelect(invokeRes.toVariable, 2))
              } else {
                (invokeRes.toVariable, stParam.toVariable)
              }
            val stPart =
              if (isMemoized(srcTarget)) {
                // create a memo closure to mark that the function invocation has been memoized
                val cc = CaseClass(CaseClassType(memoClasses(srcTarget), stTparams), targetArgs)
                stateUpdate(cc, currState)
              } else {
                currState
              }
            Let(invokeRes, invoke, Tuple(Seq(valPart, stPart)))
          } else {
            invoke
          }
          MatchCase(pattern, None, rhs)
        }
        val cases = bodyMatchCases ++
          unknownClosure(tname).map { cdef =>
            val rhs = FunctionInvocation(TypedFunDef(unknownTargets(tname), withStTparams),
              (otherParams :+ stParam).map(_.toVariable))
            val pattern = InstanceOfPattern(None, CaseClassType(cdef, recvTparams))
            MatchCase(pattern, None, rhs)
          }.toSeq
        // create a eval function
        val (params, allTparams) =
          if (stateNeedingTypes(tname)) ((recv +: otherParams :+ stParam), withStTparams)
          else (recv +: otherParams, recvTparams)
        val retType =
          if (stateUpdatingTypes(tname)) TupleType(Seq(replaceClosureTypes(retTp), stType))
          else retTp
        val dfun = new FunDef(FreshIdentifier(evalFunctionName(absdef.id.name)), allTparams map TypeParameterDef,
          params map ValDef, retType)
        //println("Creating eval function: "+dfun)
        dfun.body = Some(MatchExpr(recv.toVariable, cases))
        dfun.addFlag(Annotation("axiom", Seq()))
        (tname -> dfun)
    }
  }.toMap

  //println("State udpating types: "+stateUpdatingTypes)
  //println("state needing types: "+stateNeedingTypes)

  /**
   * These are evalFunctions that do not affect the state.
   */
  val computeFunctions = evalFunctions.collect {
    case (tname, evalfd) if stateNeedingTypes(tname) =>
      val rettpe =
        if (stateUpdatingTypes(tname)) {
          val TupleType(Seq(rt, _)) = evalfd.returnType
          rt
        } else evalfd.returnType
      val params = evalfd.params.dropRight(1) // drop the last argument
      val fun = new FunDef(FreshIdentifier(evalfd.id.name + "S", Untyped),
        evalfd.tparams, params, rettpe)
      val stTparams = evalfd.tparams.collect {
        case tpd if isPlaceHolderTParam(tpd.tp) => tpd.tp
      }
      val uiState = uninterpretedStateFor(stTparams)
      val invoke = FunctionInvocation(TypedFunDef(evalfd, evalfd.tparams.map(_.tp)),
        params.map(_.id.toVariable) :+ uiState)
      fun.body = Some(TupleSelect(invoke, 1))
      fun.addFlag(IsInlined)
      (tname -> fun)
  }.toMap

  /**
   * Create closure construction functions that is used to extract some information.
   * They are defined for each lazy class since it avoids generics and
   * simplifies the type inference (which is not full-fledged in Leon)
   */
  val closureCons = closureTnames.map { tname =>
    val absClass = absClosure(tname)
    val param1Type = AbstractClassType(absClass, absClass.tparams.map(_.tp))
    val param1 = FreshIdentifier("cc", param1Type)
    val stTparams = stateTParams.map(_ => TypeParameter.fresh("P@"))
    val param2 = FreshIdentifier("st@", stateType(stTparams))
    val tparamdefs = absClass.tparams ++ (stTparams map TypeParameterDef)
    val fun = new FunDef(FreshIdentifier(closureConsName(tname)), tparamdefs,
      Seq(ValDef(param1), ValDef(param2)), param1Type)
    fun.body = Some(param1.toVariable)
    fun.addFlag(IsInlined)
    (tname -> fun)
  }.toMap

  def mapExpr(expr: Expr)(implicit stTparams: Seq[TypeParameter]): (Option[Expr] => Expr, Boolean) = expr match {
    // ignore closure constructions inside `tmpl`
    case fi@FunctionInvocation(fd, Seq(Lambda(args, body))) if isTemplateInvocation(fi) =>
      ((st: Option[Expr]) => {
        val (tmplBodyCons, updatesState) = mapExpr(body)
        if(updatesState)
          LeonFatalError(s"Body of the template: $fi updates state!")
        FunctionInvocation(fd, Seq(Lambda(args, tmplBodyCons(st))))
      }, false) // templates cannot update state

    // (a) closure construction ?
    case l @ Lambda(_, FunctionInvocation(TypedFunDef(target, _), allArgs)) =>
      ((st: Option[Expr]) => {
        val caseClassDef = closureOfLambda(l)
        /* Result construction
          // construct a value for the result (an uninterpreted function)
          val resval = FunctionInvocation(TypedFunDef(uiFuncs(argfd)._1, tparams), flatArgs)
        }*/
        val targs = getTypeParameters(l.getType)
        val cc = CaseClass(CaseClassType(caseClassDef, targs), capturedVars(l).map(_.toVariable))
        val tname = uninstantiatedFunctionTypeName(l.getType).get
        if (st.isDefined) { // otherwise the function does not take preconditions that depend on state.
          FunctionInvocation(TypedFunDef(closureCons(tname), targs ++ stTparams), Seq(cc, st.get))
        } else cc
      }, false)

    // (b) Mem(..) construct ?
    case memc @ CaseClass(_, Seq(FunctionInvocation(TypedFunDef(target, _), args))) if isFunCons(memc) =>
      // in this case target should be a memoized function
      if (!isMemoized(target))
        throw new IllegalStateException("Argument of `Mem` should be a memoized function: " + memc)
      //println("cc: "+memoClasses(target)+" stparams: "+stTparams)
      val op = (nargs: Seq[Expr]) => ((st: Option[Expr]) => {
        CaseClass(CaseClassType(memoClasses(target), stTparams), nargs)
      }, false)
      mapNAryOperator(args, op)

    // (c) isCached check
    case cach @ FunctionInvocation(_, args) if cachedInvocation(cach) =>
      val op = (nargs: Seq[Expr]) => ((stOpt: Option[Expr]) => {
        val memClosure = nargs.head // `narg` must be a memoized closure
        ElementOfSet(memClosure, stOpt.get)
      }, false)
      mapNAryOperator(args, op)

    // (d) Pattern matching on lambdas
    case finv @ FunctionInvocation(_, Seq(CaseClass(_, Seq(cl)), Lambda(_, MatchExpr(_, mcases)))) if isFunMatch(finv) =>
      val ncases = mcases.map {
        case MatchCase(pat @ WildcardPattern(None), None, body) =>
          MatchCase(pat, None, body)
        case mc @ MatchCase(pat, Some(guard), body) =>
          val freevars = pat match {
            case TuplePattern(_, subpats) => subpats.collect {
              case InstanceOfPattern(Some(bin), _) => bin
              case WildcardPattern(Some(bin))      => bin
            }.toSet
            case InstanceOfPattern(Some(bin), _) => Set(bin)
            case WildcardPattern(Some(bin))      => Set(bin)
            case _                               => Set()
          }
          guard match {
            case finv @ FunctionInvocation(_, Seq(CaseClass(_, Seq(`cl`)), l @ Lambda(args, lbody))) if isIsFun(finv) =>
              val envVarsInGuard = (variablesOf(lbody) -- (args.map(_.id).toSet ++ freevars))
              if (!envVarsInGuard.isEmpty) {
                throw new IllegalStateException(s"Guard of $finv uses variables from the environment: $envVarsInGuard")
              }
              try {
                val tname = uninstantiatedFunctionTypeName(l.getType).get
                val uninstType = functionType(tname)
                val targs = getTypeArguments(l.getType, uninstType).get
                // here, try to create new types for the binders, they may be needed in type rectification of local variables
                val capvars = capturedVars(l)
                val ncapvars = capvars.map { id => makeIdOfType(id, replaceClosureTypes(id.getType)) }
                val realpat = CaseClassPattern(None, CaseClassType(closureOfLambda(l), targs),
                  ncapvars.map(id => WildcardPattern(Some(id))))
                MatchCase(realpat, None,
                  replaceFromIDs((capvars zip ncapvars.map(_.toVariable)).toMap, body))
              } catch {
                case _: NoSuchElementException =>
                  throw new IllegalStateException(s"Error: no Lambda in the program could match $l!")
              }
          }
      }
      mapExpr(MatchExpr(cl, ncases))

    // a solitary `is` fun invocation
    case finv @ FunctionInvocation(_, Seq(CaseClass(_, Seq(cl)), l @ Lambda(args, lbody))) if isIsFun(finv) =>
      try {
        val tname = uninstantiatedFunctionTypeName(l.getType).get
        val uninstType = functionType(tname)
        val targs = getTypeArguments(l.getType, uninstType).get
        val ncapvars = capturedVars(l).map { id => makeIdOfType(id, replaceClosureTypes(id.getType)).toVariable }
        val (nclCons, updatesState) = mapExpr(cl)
        if (updatesState)
          throw new IllegalStateException(s"Receiver $cl of `is` function call updates state!")
        ((st: Option[Expr]) =>
          Equals(nclCons(st), CaseClass(CaseClassType(closureOfLambda(l), targs), ncapvars)), false)
      } catch {
        case _: NoSuchElementException =>
          throw new IllegalStateException(s"Error: no Lambda in the program could match $l!")
      }

    // (e) withState construct
    case withst @ FunctionInvocation(_, Seq(recvr, stArg)) if isWithStateFun(withst) =>
      // recvr is a `WithStateCaseClass` and `stArg` could be arbitrary expressions returning a set of memClosures
      val CaseClass(_, Seq(exprNeedingState)) = recvr
      val (nexprCons, exprReturnsState) = mapExpr(exprNeedingState)
      val (nstCons, stArgReturnsState) = mapExpr(stArg)
      if (stArgReturnsState)
        throw new IllegalStateException("The argument of `withState` uses memoization! It should be a pure expression!" + withst)
      else {
        ((st: Option[Expr]) => {
          nexprCons(Some(nstCons(st)))
        }, exprReturnsState)
      }

    // (f) closure invocation
    case Application(lambdaExpr, args) =>
      val tname = uninstantiatedFunctionTypeName(lambdaExpr.getType).get
      val uninstType = functionType(tname)
      val dispFun = evalFunctions(tname)
      val targs = getTypeArguments(lambdaExpr.getType, uninstType).get ++ stTparams
      val op = (nargs: Seq[Expr]) => ((stOpt: Option[Expr]) => {
        val invargs =
          if (stateNeedingTypes(tname)) nargs :+ stOpt.get
          else nargs
        FunctionInvocation(TypedFunDef(dispFun, targs), invargs)
      }, stateUpdatingTypes(tname))
      mapNAryOperator(lambdaExpr +: args, op)

    // (g) `*` invocation ?
    case star @ FunctionInvocation(_, Seq(CaseClass(_, Seq(invokeExpr)))) if isStarInvocation(star) =>
      val id = (e: Expr) => e
      val (target, targs, args, retCons) = invokeExpr match {
        case Application(lambdaExpr, args) =>
          val tname = uninstantiatedFunctionTypeName(lambdaExpr.getType).get
          val uninstType = functionType(tname)
          (computeFunctions.getOrElse(tname, evalFunctions(tname)),
            getTypeArguments(lambdaExpr.getType, uninstType).get ++ stTparams,
            lambdaExpr +: args, id)
        case FunctionInvocation(TypedFunDef(tar, tps), args) =>
          // quite a few cases to consider here!
          if (funsNeedStateTps(tar)) {
            val allargs = args :+ uninterpretedStateFor(stTparams)
            val alltargs = tps ++ stTparams
            if (funsRetStates(tar)) {
              (funMap(tar), alltargs, allargs, (e: Expr) => TupleSelect(e, 1))
            } else if (funsNeedStates(tar))
              (funMap(tar), alltargs, allargs, id)
            else
              (funMap(tar), alltargs, args, id)
          } else
            (funMap(tar), tps, args, id)
      }
      val op = (nargs: Seq[Expr]) => ((st: Option[Expr]) => {
        retCons(FunctionInvocation(TypedFunDef(target, targs), nargs))
      }, false)
      mapNAryOperator(args, op)

    // (h) direct call to a memoized function ?
    case finv @ FunctionInvocation(TypedFunDef(fd, targs), args) if isMemoized(fd) =>
      mapNAryOperator(args,
        (nargs: Seq[Expr]) => ((st: Option[Expr]) => {
          val (flatArgs, letCons) = flattenArgs(nargs) // note: this is necessary to prevent measuring time of arguments twice.
          //println("handling function call: "+finv+" new args: "+nargs+" flatArgs: "+flatArgs)
          val stArgs = if (funsNeedStates(fd)) st.toSeq else Seq()
          val stparams = if (funsNeedStateTps(fd)) stTparams else Seq()
          val invoke = FunctionInvocation(TypedFunDef(funMap(fd), targs ++ stparams), flatArgs ++ stArgs)
          val invokeRes = FreshIdentifier("dres", invoke.getType, true)
          //println(s"invoking function $targetFun with args $args")
          val (valPart, currState) =
            if (funsRetStates(fd)) {
              (TupleSelect(invokeRes.toVariable, 1), TupleSelect(invokeRes.toVariable, 2))
            } else {
              (invokeRes.toVariable, st.get) // st should be defined here
            }
          // create a memo closure to mark that the function invocation has been memoized
          val cc = CaseClass(CaseClassType(memoClasses(fd), stTparams), flatArgs)
          val stPart = stateUpdate(cc, currState)
          letCons(Let(invokeRes, invoke, Tuple(Seq(valPart, stPart))))
        }, true))

    // (i) handle inst calls with arguments specially.
    // Time is assumed to ignore state always
    case finv @ FunctionInvocation(tfd, argFun) if InstUtil.instCall(finv).isDefined =>
      ((st: Option[Expr]) => {
        argFun match {
          case Seq()     => finv
          case Seq(finv) => FunctionInvocation(tfd, Seq(mapExpr(finv)._1(st)))
        }
      }, false)

    // Rest: usual language constructs
    case finv @ FunctionInvocation(TypedFunDef(fd, targs), args) if funMap.contains(fd) =>
      mapNAryOperator(args,
        (nargs: Seq[Expr]) => ((st: Option[Expr]) => {
          val stArgs =
            if (funsNeedStates(fd)) {
              st.toSeq
            } else Seq()
          val stparams =
            if (funsNeedStateTps(fd)) {
              stTparams
            } else Seq()
          FunctionInvocation(TypedFunDef(funMap(fd), targs ++ stparams), nargs ++ stArgs)
        }, funsRetStates(fd)))

    case Let(id, value, body) =>
      val (valCons, valUpdatesState) = mapExpr(value)
      val (bodyCons, bodyUpdatesState) = mapExpr(body)
      ((st: Option[Expr]) => {
        val nval = valCons(st)
        if (valUpdatesState) {
          val freshid = FreshIdentifier(id.name, nval.getType, true)
          val nextState = TupleSelect(freshid.toVariable, 2)
          val transBody = replace(Map(id.toVariable -> TupleSelect(freshid.toVariable, 1)),
            bodyCons(Some(nextState)))
          if (bodyUpdatesState)
            Let(freshid, nval, transBody)
          else
            Let(freshid, nval, Tuple(Seq(transBody, nextState)))
        } else
          Let(id, nval, bodyCons(st))
      }, valUpdatesState || bodyUpdatesState)

    case IfExpr(cond, thn, elze) =>
      val (condCons, condState) = mapExpr(cond)
      val (thnCons, thnState) = mapExpr(thn)
      val (elzeCons, elzeState) = mapExpr(elze)
      ((st: Option[Expr]) => {
        val (ncondCons, nst) =
          if (condState) {
            val cndExpr = condCons(st)
            val bder = FreshIdentifier("c", cndExpr.getType)
            val condst = TupleSelect(bder.toVariable, 2)
            ((th: Expr, el: Expr) =>
              Let(bder, cndExpr, IfExpr(TupleSelect(bder.toVariable, 1), th, el)),
              Some(condst))
          } else {
            ((th: Expr, el: Expr) => IfExpr(condCons(st), th, el), st)
          }
        val nelze =
          if ((condState || thnState) && !elzeState)
            Tuple(Seq(elzeCons(nst), nst.get))
          else elzeCons(nst)
        val nthn =
          if (!thnState && (condState || elzeState))
            Tuple(Seq(thnCons(nst), nst.get))
          else thnCons(nst)
        ncondCons(nthn, nelze)
      }, condState || thnState || elzeState)

    case MatchExpr(scr, cases) =>
      val (scrCons, scrUpdatesState) = mapExpr(scr)
      val casesRes = cases.foldLeft(Seq[(Option[Expr] => Expr, Boolean)]()) {
        case (acc, MatchCase(pat, None, rhs)) =>
          acc :+ mapExpr(rhs)
        case mcase =>
          throw new IllegalStateException("Match case with guards are not supported yet: " + mcase)
      }
      val casesUpdatesState = casesRes.exists(_._2)
      ((st: Option[Expr]) => {
        val scrExpr = scrCons(st)
        val (nscrCons, scrst) =
          if (scrUpdatesState) {
            val bder = FreshIdentifier("scr", scrExpr.getType)
            val scrst = Some(TupleSelect(bder.toVariable, 2))
            ((ncases: Seq[MatchCase]) =>
              Let(bder, scrExpr, MatchExpr(TupleSelect(bder.toVariable, 1), ncases)),
              scrst)
          } else {
            //println(s"Scrutiny does not update state: current state: $st")
            ((ncases: Seq[MatchCase]) => MatchExpr(scrExpr, ncases), st)
          }
        val ncases = (cases zip casesRes).map {
          case (MatchCase(pat, None, _), (caseCons, caseUpdatesState)) =>
            val nrhs =
              if ((scrUpdatesState || casesUpdatesState) && !caseUpdatesState)
                Tuple(Seq(caseCons(scrst), scrst.get))
              else caseCons(scrst)
            MatchCase(pat, None, nrhs)
        }
        nscrCons(ncases)
      }, scrUpdatesState || casesUpdatesState)

    // need to reset types in the case of case class constructor calls
    case CaseClass(cct, args) =>
      val ntype = replaceClosureTypes(cct).asInstanceOf[CaseClassType]
      mapNAryOperator(args,
        (nargs: Seq[Expr]) => ((st: Option[Expr]) => CaseClass(ntype, nargs), false))

    // need to reset field ids of case class select
    case CaseClassSelector(cct, clExpr, fieldId) if fieldMap.contains(fieldId) =>
      val ntype = replaceClosureTypes(cct).asInstanceOf[CaseClassType]
      val nfield = fieldMap(fieldId)
      mapNAryOperator(Seq(clExpr),
        (nargs: Seq[Expr]) => ((st: Option[Expr]) => CaseClassSelector(ntype, nargs.head, nfield), false))

    case Operator(args, op) =>
      // here, 'op' itself does not create a new state
      mapNAryOperator(args,
        (nargs: Seq[Expr]) => ((st: Option[Expr]) => op(nargs), false))

    case t: Terminal => (_ => t, false)
  }

  def mapNAryOperator(args: Seq[Expr], op: Seq[Expr] => (Option[Expr] => Expr, Boolean))(implicit stTparams: Seq[TypeParameter]) = {
    // create n variables to model n lets
    val letvars = args.map(arg => FreshIdentifier("arg", arg.getType, true).toVariable)
    (args zip letvars).foldRight(op(letvars)) {
      case ((arg, letvar), (accCons, stUpdatedBefore)) =>
        val (argCons, stUpdateFlag) = mapExpr(arg)
        val cl = if (!stUpdateFlag) {
          // here arg does not affect the newstate
          (st: Option[Expr]) => replace(Map(letvar -> argCons(st)), accCons(st))
        } else {
          // here arg does affect the newstate
          (st: Option[Expr]) =>
            {
              val narg = argCons(st)
              val argres = FreshIdentifier("a", narg.getType, true).toVariable
              val nstate = Some(TupleSelect(argres, 2))
              val letbody =
                if (stUpdatedBefore) accCons(nstate) // here, 'acc' already returns a superseeding state
                else Tuple(Seq(accCons(nstate), nstate.get)) // here, 'acc; only returns the result
              Let(argres.id, narg,
                Let(letvar.id, TupleSelect(argres, 1), letbody))
            }
        }
        (cl, stUpdatedBefore || stUpdateFlag)
    }
  }

  def assignBodiesToFunctions = {
    val paramMap: Map[Expr, Expr] = idmap.map(e => (e._1.toVariable -> e._2.toVariable))
    funMap foreach {
      case (fd, nfd) =>
        //println("Considering function: "+fd+" New fd: "+nfd)
        // Here, using name to identify 'state' parameter
        val stateParam = nfd.params.collectFirst {
          case vd if isStateParam(vd.id) => vd.id.toVariable
        }
        val stType = stateParam.map(_.getType.asInstanceOf[SetType])
        // Note: stTparams may be provided even if stParam is not required.
        val stTparams = nfd.tparams.collect {
          case tpd if isPlaceHolderTParam(tpd.tp) => tpd.tp
        }
        // TODO: we want the decreases measure to be state independent
        if (fd.hasBody) {
          val (nbodyFun, bodyUpdatesState) = mapExpr(fd.body.get)(stTparams)
          val nbody = nbodyFun(stateParam)
          val bodyWithState =
            if (!bodyUpdatesState && funsRetStates(fd))
              Tuple(Seq(nbody, stateParam.get))
            else
              nbody
          //println(s"Body of ${fd.id.name} after conversion:  ${rawBody}")
          nfd.body = Some(simplifyLets(replace(paramMap, bodyWithState)))
        }
        // Important: specifications use memoized semantics but their state changes are ignored after their execution.
        // This guarantees their observational purity/transparency collect class invariants that need to be added.
        if (fd.hasPrecondition) {
          val (npreFun, preUpdatesState) = mapExpr(fd.precondition.get)(stTparams)
          val npre = replace(paramMap, npreFun(stateParam))
          nfd.precondition =
            if (preUpdatesState)
              Some(TupleSelect(npre, 1)) // ignore state updated by pre
            else Some(npre)
        }
        // create a new result variable
        val newres =
          if (fd.hasPostcondition) {
            val Lambda(Seq(ValDef(r)), _) = fd.postcondition.get
            FreshIdentifier(r.name, nfd.returnType) //bodyType.getOrElse(nfd.returnType))
          } else FreshIdentifier("r", nfd.returnType)
        // create an output state map
        val outState =
          if (funsRetStates(fd)) { //Old code: bodyUpdatesState == Some(true) || funsRetStates(fd)
            Some(TupleSelect(newres.toVariable, 2))
          } else
            stateParam
        // create a specification that relates input-output states
        val stateRel =
          if (funsRetStates(fd)) { // add specs on states
            val stateRel =
              if (fd.annotations.contains("invstate")) Equals.apply _
              else SubsetOf.apply _
            Some(stateRel(stateParam.get, outState.get))
          } else None
        //println("stateRel: "+stateRel)

        // create a predicate that ensures that the value part is independent of the state
        val valRel =
          if (takesStateButIndep(fd)) { // add specs on value
            val uipred = uiFuncs(fd)._2.get
            val args = nfd.params.take(fd.params.size).map(_.id.toVariable)
            val retarg =
              if (funsRetStates(fd))
                TupleSelect(newres.toVariable, 1)
              else newres.toVariable
            // Note: here we ignore state type-parameters by using fd.tparams
            Some(FunctionInvocation(TypedFunDef(uipred, fd.tparams.map(_.tp)), args :+ retarg))
          } else None

        val targetPost =
          if (fd.hasPostcondition) {
            val Lambda(Seq(ValDef(resid)), post) = fd.postcondition.get
            val resval =
              if (funsRetStates(fd))
                TupleSelect(newres.toVariable, 1)
              else newres.toVariable
            // thread state through postcondition
            val (npostFun, postUpdatesState) = mapExpr(post)(stTparams)
            // bind calls to instate and outstate calls to their respective values
            val tpost = simplePostTransform {
              case e if isInStateCall(e)  => stateParam.get
              case e if isOutStateCall(e) => outState.get
              case e                         => e
            }(replace(paramMap ++ Map(resid.toVariable -> resval), npostFun(outState)))
            val npost =
              if (postUpdatesState) {
                TupleSelect(tpost, 1) // ignore state updated by post
              } else
                tpost
            Some(npost)
          } else {
            None
          }
        // try to add to the body of a let (if it exists) so that it is easy to extract the resource spec.
        val addPosts = stateRel.toList ++ valRel.toList
        val nfdPost = targetPost match {
          case Some(post) =>
            val (letsCons, letsBody) = letStarUnapply(simplifyLetsAndLetsWithTuples(post))
            letsBody match {
              case And(args) => letsCons(createAnd(addPosts ++ args))
              case p =>
                if (exists(InstUtil.instCall(_).isDefined)(p) && exists(_.isInstanceOf[And])(p)) {
                  ctx.reporter.warning(s"Postcondition of ${fd.id} has resource template in conjunctions which cannot be separated!")
                }
                letsCons(createAnd(addPosts :+ p))
            }
          case _ => createAnd(addPosts)
        }
        nfd.postcondition = Some(Lambda(Seq(ValDef(newres)), nfdPost))
      case _ =>
    }
  }

  def assignContractsForEvals = evalFunctions.foreach {
    case (tname, evalfd) =>
      val cdefs = concreteClosures(tname)
      val relTparams = evalfd.tparams.collect {
        case tdef if !isPlaceHolderTParam(tdef.tp) => tdef.tp
      }
      val postres = FreshIdentifier("res", evalfd.returnType)
      val postMatchCases = cdefs map { cdef =>
        // create a body of the match (which asserts that return value equals the uninterpreted function)
        // and also that the result field equals the result
        val target = targetOfClosure(cdef).get
        val ctype = CaseClassType(cdef, getTypeParameters(evalfd.params.head.getType))
        val binder = FreshIdentifier("t", ctype)
        val pattern = InstanceOfPattern(Some(binder), ctype)
        // Deals with Result
        // (i) t.clres == res._1
        //        val clause1 = if (!ismem) {
        //          val clresField = cdef.fields.last
        //          Equals(TupleSelect(postres.toVariable, 1),
        //            CaseClassSelector(ctype, binder.toVariable, clresField.id))
        //        } else
        //          Util.tru
        // (ii) res._1 == uifun(args)
        val clause2 = if (takesStateButIndep(target)) {
          val flds = cdef.fields
          //            if (!ismem) cdef.fields.dropRight(1)
          val args = flds map {
            fld => CaseClassSelector(ctype, binder.toVariable, fld.id)
          }
          Some(Equals(TupleSelect(postres.toVariable, 1),
            FunctionInvocation(TypedFunDef(uiFuncs(target)._1, relTparams), args)))
        } else None
        val rhs = createAnd(clause2.toList)
        MatchCase(pattern, None, rhs)
      }
      // create a default case to match other cases (esp. the unknown external function)
      val defaultRhs = if (escapingTypes(tname)) {
        val stateParam = evalfd.params.collectFirst { case vd if isStateParam(vd.id) => vd.id.toVariable }
        SubsetOf(stateParam.get, TupleSelect(postres.toVariable, 2))
      } else Util.tru
      val default = MatchCase(WildcardPattern(None), None, defaultRhs)
      evalfd.postcondition = Some(
        Lambda(Seq(ValDef(postres)),
          MatchExpr(evalfd.params.head.toVariable, postMatchCases :+ default)))
  }

  /**
   * Overrides the types of the lazy fields  in the case class definitions
   * Note: here we reset CaseClass fields instead of having to duplicate the
   * entire class hierarchy.
   */
  var fieldMap = Map[Identifier, Identifier]()
  def copyField(oldId: Identifier, tpe: TypeTree): Identifier = {
    val freshid = FreshIdentifier(oldId.name, tpe)
    fieldMap += (oldId -> freshid)
    freshid
  }

  def transformCaseClasses = p.definedClasses.foreach {
    case ccd :CaseClassDef if !ccd.flags.contains(Annotation("library", Seq())) =>
      val nfields = ccd.fields.map { fld =>
        val nt = replaceClosureTypes(fld.getType)
        if (nt != fld.getType) {
          //println(s"AbsType: $clType type args: $typeArgs")
          ValDef(copyField(fld.id, nt))
        } else fld
      }
      ccd.setFields(nfields)
    case _ => ;
  }

  def apply: Program = {
    transformCaseClasses
    assignBodiesToFunctions
    assignContractsForEvals

    // Ideally, the lazy closure will be added to a separate module
    // and imported every where
    val mainModule = p.units.find(_.isMainUnit).get.modules.head
    ProgramUtil.appendDefsToModules(
      copyProgram(p,
        (defs: Seq[Definition]) => defs.flatMap {
          case fd: FunDef if funMap.contains(fd) =>
            uiFuncs.get(fd) match {
              case Some((funui, Some(predui))) =>
                Seq(funMap(fd), funui, predui)
              case Some((funui, _)) =>
                Seq(funMap(fd), funui)
              case _ => Seq(funMap(fd))
            }
          case d => Seq(d)
        }),
      Map(mainModule -> (allClosuresAndParents ++ memoClosures.toSeq ++
        closureCons.values ++ evalFunctions.values ++ unknownTargets.values ++
        computeFunctions.values :+ uninterpretedState)))
  }
}
