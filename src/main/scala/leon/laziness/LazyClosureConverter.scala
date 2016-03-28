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
import leon.invariant.util.TypeUtil._
import LazinessUtil._
import ProgramUtil._
import PredicateUtil._
import purescala.TypeOps.bestRealType

/**
 * (a) add state to every function in the program
 * (b) thread state through every expression in the program sequentially
 * (c) replace lazy constructions with case class creations
 * (d) replace isEvaluated with currentState.contains()
 * (e) replace accesses to $.value with calls to dispatch with current state
 */
class LazyClosureConverter(p: Program, ctx: LeonContext,
                           closureFactory: LazyClosureFactory,
                           funsManager: LazyFunctionsManager) {
  val debug = false
  // flags
  //val removeRecursionViaEval = false
  val refEq = ctx.findOptionOrDefault(LazinessEliminationPhase.optRefEquality)

  val funsNeedStates = funsManager.funsNeedStates
  val funsRetStates = funsManager.funsRetStates
  val starCallers = funsManager.funsNeedStateTps
  val lazyTnames = closureFactory.lazyTypeNames
  val lazyops = closureFactory.lazyops

  /**
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

  val funMap = p.definedFunctions.collect {
    case fd if (fd.hasBody && !fd.isLibrary && !fd.isInvariant) => // skipping class invariants for now.
      // replace lazy types in parameters and return values
      val nparams = fd.params map { vd =>
        val nparam = makeIdOfType(vd.id, replaceLazyTypes(vd.getType))
        ValDef(nparam)
      }
      val nretType = replaceLazyTypes(fd.returnType)
      val stparams =
        if (funsNeedStates(fd) || starCallers(fd))
          // create fresh type parameters for the state
          closureFactory.state.tparams.map(_ => TypeParameter.fresh("P@"))
        else Seq()

      val nfd = if (funsNeedStates(fd)) { // this also includes lazy constructors
        val stType = CaseClassType(closureFactory.state, stparams)
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
      } else {
        new FunDef(FreshIdentifier(fd.id.name), fd.tparams ++ (stparams map TypeParameterDef),
          nparams, nretType)
      }
      // copy annotations
      fd.flags.foreach(nfd.addFlag(_))
      (fd -> nfd)
  }.toMap

  // were used for optimization purposes
  //  lazy val uiTarges = funMap.collect {
  //    case (k, v) if closureFactory.isLazyOp(k) =>
  //      val ufd = new FunDef(FreshIdentifier(v.id.name, v.id.getType, true),
  //        v.tparams, v.params, v.returnType)
  //      (k -> ufd)
  //  }.toMap

  //TODO: Optimization: we can omit come functions whose translations will not be recursive.
  def takesStateButIndep(fd: FunDef) =
    funsNeedStates(fd) && funsManager.hasStateIndependentBehavior(fd)

  /**
   * A set of uninterpreted functions that are used
   * in specs to ensure that value part is independent of the state
   */
  val uiFuncs: Map[FunDef, (FunDef, Option[FunDef])] = funMap.collect {
    case (k, v) if takesStateButIndep(k) =>
      val params = v.params.take(k.params.size) // ignore the state params
      val retType =
        if (funsRetStates(k)) {
          val TupleType(valtype +: _) = v.returnType
          valtype
        } else v.returnType
      val tparams = (params.map(_.getType) :+ retType).flatMap(getTypeParameters(_)).distinct
      val tparamsDef = tparams.map(TypeParameterDef(_))
      val ufd = new FunDef(FreshIdentifier(v.id.name + "UI"), tparamsDef, params, retType)

      // we also need to create a function that assumes that the result equals
      // the uninterpreted function
      val valres = ValDef(FreshIdentifier("valres", retType))
      val pred = new FunDef(FreshIdentifier(v.id.name + "ValPred"), tparamsDef,
        params :+ valres, BooleanType)
      val resid = FreshIdentifier("res", pred.returnType)
      pred.fullBody = Ensuring(
        Equals(valres.id.toVariable,
          FunctionInvocation(TypedFunDef(ufd, tparams), params.map(_.id.toVariable))), // res = funUI(..)
        Lambda(Seq(ValDef(resid)), resid.toVariable)) // holds
      pred.addFlag(Annotation("axiom", Seq())) // @axiom is similar to @library
      (k -> (ufd, Some(pred)))

    case (k, v) if lazyops(k) =>
      // here 'v' cannot for sure take state params, otherwise it must be state indep
      if (funsNeedStates(k))
        throw new IllegalStateException("Lazyop that has a state dependent behavior: " + k)
      else {
        val tparams = (v.params.map(_.getType) :+ v.returnType).flatMap(getTypeParameters(_)).distinct
        val tparamsDef = tparams.map(TypeParameterDef(_))
        val ufd = new FunDef(FreshIdentifier(v.id.name + "UI"), tparamsDef, v.params, v.returnType)
        (k -> (ufd, None))
      }
  }.toMap

  /**
   * A set of uninterpreted functions that return fixed but uninterpreted states
   * Note: here I am using mutation on purpose to create uninterpreted states on
   * demand.
   */
  var uiStateFuns = Map[String, FunDef]()
  def getUninterpretedState(lazyTypename: String, tparams: Seq[TypeParameter]) = {
    val uiStateFun = if (uiStateFuns.contains(lazyTypename)) {
      uiStateFuns(lazyTypename)
    } else {
      // create a body-less fundef that will return a state
      val stType = CaseClassType(closureFactory.state, closureFactory.state.tparams.map(_.tp))
      val fd = new FunDef(FreshIdentifier("ui" + lazyTypename), closureFactory.state.tparams, Seq(), stType)
      uiStateFuns += (lazyTypename -> fd)
      fd
    }
    FunctionInvocation(TypedFunDef(uiStateFun, tparams), Seq())
  }

  def replaceLazyTypes(t: TypeTree): TypeTree = {
    unwrapLazyType(t) match {
      case None =>
        val NAryType(tps, tcons) = t
        tcons(tps map replaceLazyTypes)
      case Some(btype) =>
        val absClass = closureFactory.absClosureType(typeNameWOParams(btype))
        val ntype = AbstractClassType(absClass, getTypeParameters(btype))
        val NAryType(tps, tcons) = ntype
        tcons(tps map replaceLazyTypes)
    }
  }

  /**
   * Create dispatch functions for each lazy type.
   * Note: the dispatch functions will be annotated as library so that
   * their pre/posts are not checked (the fact that they hold are verified separately)
   * Note that by using 'assume-pre' we can also assume the preconditions of closures at
   * the call-sites.
   */
  val evalFunctions = lazyTnames.map { tname =>
    val ismem = closureFactory.isMemType(tname)
    val tpe = /*freshenTypeArguments(*/ closureFactory.lazyType(tname) //)
    val absdef = closureFactory.absClosureType(tname)
    val cdefs = closureFactory.closures(tname)

    // construct parameters and return types
    val recvTparams = getTypeParameters(tpe)
    val stTparams = closureFactory.state.tparams.map(_ => TypeParameter.fresh("P@"))
    val param1 = FreshIdentifier("cl", AbstractClassType(absdef, recvTparams))
    val stType = CaseClassType(closureFactory.state, stTparams)
    val param2 = FreshIdentifier("st@", stType)
    val retType = TupleType(Seq(tpe, stType))

    // create a eval function
    val dfun = new FunDef(FreshIdentifier(evalFunctionName(absdef.id.name)),
      (recvTparams ++ stTparams) map TypeParameterDef,
      Seq(ValDef(param1), ValDef(param2)), retType)

    //println("Creating eval function: "+dfun)
    // assign body of the eval fucntion
    // create a match case to switch over the possible class defs and invoke the corresponding functions
    val bodyMatchCases = cdefs map { cdef =>
      val ctype = CaseClassType(cdef, recvTparams) // we assume that the type parameters of cdefs are same as absdefs
      val binder = FreshIdentifier("t", ctype)
      val pattern = InstanceOfPattern(Some(binder), ctype)
      // create a body of the match
      // the last field represents the result (only if the type is a susp type)
      val flds =
        if (!ismem) cdef.fields.dropRight(1)
        else cdef.fields
      val args = flds map { fld =>
        CaseClassSelector(ctype, binder.toVariable, fld.id)
      }
      val op = closureFactory.caseClassToOp(cdef)
      val targetFun = funMap(op)
      // invoke the target fun with appropriate values
      val invoke =
        if (funsNeedStates(op))
          FunctionInvocation(TypedFunDef(targetFun, recvTparams ++ stTparams), args :+ param2.toVariable)
        else
          FunctionInvocation(TypedFunDef(targetFun, recvTparams), args)
      val invokeRes = FreshIdentifier("dres", invoke.getType)
      //println(s"invoking function $targetFun with args $args")
      val updateFun = TypedFunDef(closureFactory.stateUpdateFuns(tname), stTparams)
      val (valPart, stPart) =
        if (funsRetStates(op)) {
          val invokeSt = TupleSelect(invokeRes.toVariable, 2)
          val nst = FunctionInvocation(updateFun, Seq(invokeSt, binder.toVariable))
          (TupleSelect(invokeRes.toVariable, 1), nst)
        } else {
          val nst = FunctionInvocation(updateFun, Seq(param2.toVariable, binder.toVariable))
          (invokeRes.toVariable, nst)
        }
      val rhs = Let(invokeRes, invoke, Tuple(Seq(valPart, stPart)))
      MatchCase(pattern, None, rhs)
    }
    val cases = if (!ismem) {
      // create a new match case for eager evaluation
      val eagerDef = closureFactory.eagerClosure(tname).get
      val ctype = CaseClassType(eagerDef, recvTparams)
      val binder = FreshIdentifier("t", ctype)
      // create a body of the match
      val valPart = CaseClassSelector(ctype, binder.toVariable, eagerDef.fields(0).id)
      val rhs = Tuple(Seq(valPart, param2.toVariable)) // state doesn't change for eager closure
      MatchCase(InstanceOfPattern(Some(binder), ctype), None, rhs) +: bodyMatchCases
    } else
      bodyMatchCases
    dfun.body = Some(MatchExpr(param1.toVariable, cases))
    dfun.addFlag(Annotation("axiom", Seq()))
    (tname -> dfun)
  }.toMap

  /**
   * These are evalFunctions that do not affect the state.
   */
  val computeFunctions = evalFunctions.map {
    case (tname, evalfd) =>
      val tpe = /*freshenTypeArguments(*/ closureFactory.lazyType(tname) //)
      val param1 = evalfd.params.head
      val fun = new FunDef(FreshIdentifier(evalfd.id.name + "*", Untyped),
        evalfd.tparams, Seq(param1), tpe)
      val stTparams = evalfd.tparams.collect {
        case tpd if isPlaceHolderTParam(tpd.tp) => tpd.tp
      }
      val uiState = getUninterpretedState(tname, stTparams)
      val invoke = FunctionInvocation(TypedFunDef(evalfd, evalfd.tparams.map(_.tp)),
        Seq(param1.id.toVariable, uiState))
      fun.body = Some(TupleSelect(invoke, 1))
      fun.addFlag(IsInlined)
      (tname -> fun)
  }.toMap

  /**
   * Create closure construction functions that ensures a postcondition.
   * They are defined for each lazy class since it avoids generics and
   * simplifies the type inference (which is not full-fledged in Leon)
   */
  val closureCons = lazyTnames.map { tname =>
    val adt = closureFactory.absClosureType(tname)
    val param1Type = AbstractClassType(adt, adt.tparams.map(_.tp))
    val param1 = FreshIdentifier("cc", param1Type)
    val stTparams = closureFactory.state.tparams.map(_ => TypeParameter.fresh("P@"))
    val stType = CaseClassType(closureFactory.state, stTparams)
    val param2 = FreshIdentifier("st@", stType)
    val tparamdefs = adt.tparams ++ (stTparams map TypeParameterDef)
    val fun = new FunDef(FreshIdentifier(closureConsName(tname)), tparamdefs,
      Seq(ValDef(param1), ValDef(param2)), param1Type)
    fun.body = Some(param1.toVariable)
    fun.addFlag(IsInlined)
    // assert that the closure in unevaluated if useRefEquality is enabled! is this needed ?
    // not supported as of now
    /*if (refEq) {
      val resid = FreshIdentifier("res", param1Type)
      val postbody = Not(ElementOfSet(resid.toVariable, param2.toVariable))
      fun.postcondition = Some(Lambda(Seq(ValDef(resid)), postbody))
      fun.addFlag(Annotation("axiom", Seq()))
    }*/
    (tname -> fun)
  }.toMap

  def mapExpr(expr: Expr)(implicit stTparams: Seq[TypeParameter]): (Option[Expr] => Expr, Boolean) = expr match {

    case finv @ FunctionInvocation(_, Seq(Lambda(_, FunctionInvocation(TypedFunDef(argfd, tparams), args)))) // lazy construction ?
    if isLazyInvocation(finv)(p) =>
      val op = (nargs: Seq[Expr]) => ((st: Option[Expr]) => {
        val adt = closureFactory.closureOfLazyOp(argfd)
        // create lets to bind the nargs to variables
        val (flatArgs, letCons) = nargs.foldRight((Seq[Variable](), (e: Expr) => e)) {
          case (narg, (fargs, lcons)) =>
            val id = FreshIdentifier("a", narg.getType, true)
            (id.toVariable +: fargs, e => Let(id, narg, lcons(e)))
        }
        val ccArgs = if (!isMemoized(argfd)) {
          // construct a value for the result (an uninterpreted function)
          val resval = FunctionInvocation(TypedFunDef(uiFuncs(argfd)._1, tparams), flatArgs)
          flatArgs :+ resval
        } else
          flatArgs
        val cc = CaseClass(CaseClassType(adt, tparams), ccArgs)
        val baseLazyTypeName = closureFactory.lazyTypeNameOfClosure(adt)
        val fi = FunctionInvocation(TypedFunDef(closureCons(baseLazyTypeName), tparams ++ stTparams),
          Seq(cc, st.get))
        letCons(fi) // this could be 'fi' wrapped into lets
      }, false)
      mapNAryOperator(args, op)

    case cc @ CaseClass(_, Seq(FunctionInvocation(TypedFunDef(argfd, tparams), args))) if isMemCons(cc)(p) =>
      // in this case argfd is a memoized function
      val op = (nargs: Seq[Expr]) => ((st: Option[Expr]) => {
        val adt = closureFactory.closureOfLazyOp(argfd)
        CaseClass(CaseClassType(adt, tparams), nargs)
      }, false)
      mapNAryOperator(args, op)

    case finv @ FunctionInvocation(_, Seq(Lambda(_, arg))) if isEagerInvocation(finv)(p) =>
      // here arg is guaranteed to be a variable
      ((st: Option[Expr]) => {
        val rootType = bestRealType(arg.getType)
        val tname = typeNameWOParams(rootType)
        val tparams = getTypeArguments(rootType)
        val eagerClosure = closureFactory.eagerClosure(tname).get
        CaseClass(CaseClassType(eagerClosure, tparams), Seq(arg))
      }, false)

    case finv @ FunctionInvocation(_, args) if isEvaluatedInvocation(finv)(p) => // isEval function ?
      val op = (nargs: Seq[Expr]) => ((stOpt: Option[Expr]) => {
        val narg = nargs(0) // there must be only one argument here
        val baseType = unwrapLazyType(narg.getType).get
        val tname = typeNameWOParams(baseType)
        val st = stOpt.get
        val stType = CaseClassType(closureFactory.state, stTparams)
        val cls = closureFactory.selectFieldOfState(tname, st, stType)
        val memberTest = ElementOfSet(narg, cls)
        val subtypeTest = IsInstanceOf(narg,
          CaseClassType(closureFactory.eagerClosure(tname).get, getTypeArguments(baseType)))
        Or(memberTest, subtypeTest)
      }, false)
      mapNAryOperator(args, op)

    case finv @ FunctionInvocation(_, args) if isCachedInv(finv)(p) => // isCached function ?
      val baseType = unwrapLazyType(args(0).getType).get
      val op = (nargs: Seq[Expr]) => ((stOpt: Option[Expr]) => {
        val narg = nargs(0) // there must be only one argument here
        //println("narg: "+narg+" type: "+narg.getType)
        val tname = typeNameWOParams(baseType)
        val st = stOpt.get
        val stType = CaseClassType(closureFactory.state, stTparams)
        val cls = closureFactory.selectFieldOfState(tname, st, stType)
        ElementOfSet(narg, cls)
      }, false)
      mapNAryOperator(args, op)

    case finv @ FunctionInvocation(_, Seq(recvr, funcArg)) if isSuspInvocation(finv)(p) =>
      ((st: Option[Expr]) => {
        // `funcArg` is a closure whose body is a function invocation
        //TODO: make sure the function is not partially applied in the body
        funcArg match {
          case Lambda(_, FunctionInvocation(TypedFunDef(fd, _), _)) =>
            // retrieve the case-class for the operation from the factory
            val caseClass = closureFactory.closureOfLazyOp(fd)
            val targs = TypeUtil.getTypeArguments(unwrapLazyType(recvr.getType).get)
            val caseClassType = CaseClassType(caseClass, targs)
            IsInstanceOf(recvr, caseClassType)
          case _ =>
            throw new IllegalArgumentException("The argument to isSuspension should be " +
              "a partially applied function of the form: <method-name> _")
        }
      }, false)

    case finv @ FunctionInvocation(_, Seq(recvr, stArgs @ _*)) if isWithStateFun(finv)(p) =>
      // recvr is a `WithStateCaseClass` and `stArgs` could be arbitrary expressions that return values of types of fields of state
      val numStates = closureFactory.state.fields.size
      if (stArgs.size != numStates)
        throw new IllegalStateException("The arguments to `withState` should equal the number of states: " + numStates)

      val CaseClass(_, Seq(exprNeedingState)) = recvr
      val (nexprCons, exprReturnsState) = mapExpr(exprNeedingState)
      val nstConses = stArgs map mapExpr
      if (nstConses.exists(_._2)) // any 'stArg' returning state
        throw new IllegalStateException("One of the  arguments to `withState` returns a new state, which is not supported: " + finv)
      else {
        ((st: Option[Expr]) => {
          // create a new state using the nstConses
          val nstSets = nstConses map { case (stCons, _) => stCons(st) }
          val tparams = nstSets.flatMap(nst => getTypeParameters(nst.getType)).distinct
          val nst = CaseClass(CaseClassType(closureFactory.state, tparams), nstSets)
          nexprCons(Some(nst))
        }, exprReturnsState)
      }

    case finv @ FunctionInvocation(_, args) if isValueInvocation(finv)(p) => // is  value function ?
      val op = (nargs: Seq[Expr]) => ((stOpt: Option[Expr]) => {
        val st = stOpt.get
        val baseType = unwrapLazyType(nargs(0).getType).get // there must be only one argument here
        val tname = typeNameWOParams(baseType)
        val dispFun = evalFunctions(tname)
        val tparams = (getTypeParameters(baseType) ++ stTparams).distinct
        FunctionInvocation(TypedFunDef(dispFun, tparams), nargs :+ st)
      }, true)
      mapNAryOperator(args, op)

    case finv @ FunctionInvocation(_, args) if isStarInvocation(finv)(p) => // is * function ?
      val op = (nargs: Seq[Expr]) => ((st: Option[Expr]) => {
        val baseType = unwrapLazyType(nargs(0).getType).get // there must be only one argument here
        val tname = typeNameWOParams(baseType)
        val dispFun = computeFunctions(tname)
        val tparams = getTypeParameters(baseType) ++ stTparams
        FunctionInvocation(TypedFunDef(dispFun, tparams), nargs)
      }, false)
      mapNAryOperator(args, op)

    case FunctionInvocation(TypedFunDef(fd, tparams), args) if funMap.contains(fd) =>
      mapNAryOperator(args,
        (nargs: Seq[Expr]) => ((st: Option[Expr]) => {
          val stArgs =
            if (funsNeedStates(fd)) {
              st.toSeq
            } else Seq()
          val stparams =
            if (funsNeedStates(fd) || starCallers(fd)) {
              stTparams
            } else Seq()
          FunctionInvocation(TypedFunDef(funMap(fd), tparams ++ stparams), nargs ++ stArgs)
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
      val ntype = replaceLazyTypes(cct).asInstanceOf[CaseClassType]
      mapNAryOperator(args,
        (nargs: Seq[Expr]) => ((st: Option[Expr]) => CaseClass(ntype, nargs), false))

    // need to reset field ids of case class select
    case CaseClassSelector(cct, clExpr, fieldId) if fieldMap.contains(fieldId) =>
      val ntype = replaceLazyTypes(cct).asInstanceOf[CaseClassType]
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

  def fieldsOfState(st: Expr, stType: CaseClassType): Seq[Expr] = {
    closureFactory.lazyTypeNames.map { tn =>
      closureFactory.selectFieldOfState(tn, st, stType)
    }
  }

  def assignBodiesToFunctions = {
    val paramMap: Map[Expr, Expr] = idmap.map(e => (e._1.toVariable -> e._2.toVariable))
    funMap foreach {
      case (fd, nfd) =>
        //println("Considering function: "+fd)
        // Here, using name to identify 'state' parameters
        val stateParam = nfd.params.collectFirst {
          case vd if isStateParam(vd.id) =>
            vd.id.toVariable
        }
        val stType = stateParam.map(_.getType.asInstanceOf[CaseClassType])
        // Note: stTparams may be provided even if stParam is not required.
        val stTparams = nfd.tparams.collect {
          case tpd if isPlaceHolderTParam(tpd.tp) => tpd.tp
        }
        val (nbodyFun, bodyUpdatesState) = mapExpr(fd.body.get)(stTparams)
        val nbody = nbodyFun(stateParam)
        val bodyWithState =
          if (!bodyUpdatesState && funsRetStates(fd))
            Tuple(Seq(nbody, stateParam.get))
          else
            nbody
        nfd.body = Some(simplifyLets(replace(paramMap, bodyWithState)))
        //println(s"Body of ${fd.id.name} after conversion&simp:  ${nfd.body}")

        // Important: specifications use lazy semantics but
        // their state changes are ignored after their execution.
        // This guarantees their observational purity/transparency
        // collect class invariants that need to be added
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
            FreshIdentifier(r.name, bodyWithState.getType)
          } else FreshIdentifier("r", nfd.returnType)

        // create an output state map
        val outState =
          if (bodyUpdatesState || funsRetStates(fd)) {
            Some(TupleSelect(newres.toVariable, 2))
          } else
            stateParam

        // create a specification that relates input-output states
        val stateRel =
          if (funsRetStates(fd)) { // add specs on states
            val instates = fieldsOfState(stateParam.get, stType.get)
            val outstates = fieldsOfState(outState.get, stType.get)
            val stateRel =
              if (fd.annotations.contains("invstate")) Equals.apply _
              else SubsetOf.apply _
            Some(createAnd((instates zip outstates).map(p => stateRel(p._1, p._2))))
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
            Some(FunctionInvocation(TypedFunDef(uipred, nfd.tparams.map(_.tp)),
              args :+ retarg))
          } else None

        val targetPost =
          if (fd.hasPostcondition) {
            val Lambda(Seq(ValDef(resid)), post) = fd.postcondition.get
            val resval =
              if (bodyUpdatesState || funsRetStates(fd))
                TupleSelect(newres.toVariable, 1)
              else newres.toVariable
            // thread state through postcondition
            val (npostFun, postUpdatesState) = mapExpr(post)(stTparams)
            // bind calls to instate and outstate calls to their respective values
            val tpost = simplePostTransform {
              case e if LazinessUtil.isInStateCall(e)(p) =>
                val baseType = getTypeArguments(e.getType).head
                val tname = typeNameWOParams(baseType)
                closureFactory.selectFieldOfState(tname, stateParam.get, stType.get)

              case e if LazinessUtil.isOutStateCall(e)(p) =>
                val baseType = getTypeArguments(e.getType).head
                val tname = typeNameWOParams(baseType)
                closureFactory.selectFieldOfState(tname, outState.get, stType.get)

              case e => e
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
        nfd.postcondition = Some(Lambda(Seq(ValDef(newres)),
          createAnd(stateRel.toList ++ valRel.toList ++ targetPost.toList)))
    }
  }

  def assignContractsForEvals = evalFunctions.foreach {
    case (tname, evalfd) =>
      val ismem = closureFactory.isMemType(tname)
      val cdefs = closureFactory.closures(tname)
      val recvTparams = getTypeParameters(evalfd.params.head.getType)
      val postres = FreshIdentifier("res", evalfd.returnType)
      val postMatchCases = cdefs map { cdef =>
        // create a body of the match (which asserts that return value equals the uninterpreted function)
        // and also that the result field equals the result
        val op = closureFactory.lazyopOfClosure(cdef)
        val ctype = CaseClassType(cdef, recvTparams)
        val binder = FreshIdentifier("t", ctype)
        val pattern = InstanceOfPattern(Some(binder), ctype)
        // t.clres == res._1
        val clause1 = if (!ismem) {
          val clresField = cdef.fields.last
          Equals(TupleSelect(postres.toVariable, 1),
            CaseClassSelector(ctype, binder.toVariable, clresField.id))
        } else
          Util.tru
        //res._1 == uifun(args)
        val clause2 = if (takesStateButIndep(op)) {
          val flds =
            if (!ismem) cdef.fields.dropRight(1)
            else cdef.fields
          val args = flds map {
            fld => CaseClassSelector(ctype, binder.toVariable, fld.id)
          }
          Some(Equals(TupleSelect(postres.toVariable, 1),
            FunctionInvocation(TypedFunDef(uiFuncs(op)._1, recvTparams), args)))
        } else None
        val rhs = createAnd(clause1 +: clause2.toList)
        MatchCase(pattern, None, rhs)
      }
      // create a default case ot match other cases
      val default = MatchCase(WildcardPattern(None), None, Util.tru)
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
    case ccd: CaseClassDef if !ccd.flags.contains(Annotation("library", Seq())) &&
      ccd.fields.exists(vd => isLazyType(vd.getType)) =>
      val nfields = ccd.fields.map { fld =>
        unwrapLazyType(fld.getType) match {
          case None => fld
          case Some(btype) =>
            val clType = closureFactory.absClosureType(typeNameWOParams(btype))
            val typeArgs = getTypeArguments(btype)
            //println(s"AbsType: $clType type args: $typeArgs")
            val adtType = AbstractClassType(clType, typeArgs)
            ValDef(copyField(fld.id, adtType))
        }
      }
      ccd.setFields(nfields)
    case _ => ;
  }

  def apply: Program = {
    // TODO: for now pick a arbitrary point to add new defs. But ideally the lazy closure will be added to a separate module
    // and imported every where
    val anchor = funMap.values.last
    transformCaseClasses
    assignBodiesToFunctions
    assignContractsForEvals
    ProgramUtil.addDefs(
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
      closureFactory.allClosuresAndParents ++ Seq(closureFactory.state) ++
        closureCons.values ++ evalFunctions.values ++
        computeFunctions.values ++ uiStateFuns.values ++
        closureFactory.stateUpdateFuns.values, anchor)
  }
}
