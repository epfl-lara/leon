package leon
package laziness

import invariant.factories._
import invariant.util.Util._
import invariant.util._
import invariant.structure.FunctionUtils._
import purescala.ScalaPrinter
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Extractors._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import leon.invariant.util.LetTupleSimplification._
import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter
import scala.util.matching.Regex
import leon.purescala.PrettyPrinter
import leon.LeonContext
import leon.LeonOptionDef
import leon.Main
import leon.TransformationPhase
import LazinessUtil._
import ProgramUtil._
import PredicateUtil._
import purescala.TypeOps._

/**
 * (a) add state to every function in the program
 * (b) thread state through every expression in the program sequentially
 * (c) replace lazy constructions with case class creations
 * (d) replace isEvaluated with currentState.contains()
 * (e) replace accesses to $.value with calls to dispatch with current state
 */
class LazyClosureConverter(p: Program, ctx: LeonContext, closureFactory: LazyClosureFactory) {
  val debug = false
  // flags
  //val removeRecursionViaEval = false
  val useRefEquality = ctx.findOption(LazinessEliminationPhase.optRefEquality).getOrElse(false)

  val funsManager = new LazyFunctionsManager(p)
  val funsNeedStates = funsManager.funsNeedStates
  val funsRetStates = funsManager.funsRetStates
  val tnames = closureFactory.lazyTypeNames

  // create a mapping from functions to new functions
  lazy val funMap = p.definedFunctions.collect {
    case fd if (fd.hasBody && !fd.isLibrary) =>
      // replace lazy types in parameters and return values
      val nparams = fd.params map { vd =>
        ValDef(vd.id, Some(replaceLazyTypes(vd.getType))) // override type of identifier
      }
      val nretType = replaceLazyTypes(fd.returnType)
      val nfd = if (funsNeedStates(fd)) {
        var newTParams = Seq[TypeParameterDef]()
        val stTypes = tnames map { tn =>
          val absClass = closureFactory.absClosureType(tn)
          val tparams = absClass.tparams.map(_ =>
            TypeParameter.fresh("P@"))
          newTParams ++= tparams map TypeParameterDef
          SetType(AbstractClassType(absClass, tparams))
        }
        val stParams = stTypes.map { stType =>
          ValDef(FreshIdentifier("st@", stType, true))
        }
        val retTypeWithState =
          if (funsRetStates(fd))
            TupleType(nretType +: stTypes)
          else
            nretType
        // the type parameters will be unified later
        new FunDef(FreshIdentifier(fd.id.name, Untyped),
          fd.tparams ++ newTParams, nparams ++ stParams, retTypeWithState)
        // body of these functions are defined later
      } else {
        new FunDef(FreshIdentifier(fd.id.name, Untyped), fd.tparams, nparams, nretType)
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

  /**
   * A set of uninterpreted functions that are used
   * in specs to ensure that value part is independent of the state
   */
  val uiFuncs = funMap.collect {
    case (k, v) if funsNeedStates(k) &&
      funsManager.hasStateIndependentBehavior(k) => //TODO: we can omit come functions whose translations will not be recursive.

      val params = v.params.take(k.params.size) // ignore the state params
      val retType =
        if (funsRetStates(k)) {
          val TupleType(valtype +: _) = v.returnType
          valtype
        } else v.returnType
      val tparams = (params.map(_.getType) :+ retType).flatMap(getTypeParameters(_)).distinct
      val tparamsDef =  tparams.map(TypeParameterDef(_))
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
      pred.addFlag(Annotation("axiom", Seq())) // mark it as @library
      (k -> (ufd, pred))
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
      val absClass = closureFactory.absClosureType(lazyTypename)
      val initTparams = absClass.tparams.map(_.tp)
      val stType = SetType(AbstractClassType(absClass, initTparams))
      val fd = new FunDef(FreshIdentifier("ui" + lazyTypename), absClass.tparams, Seq(), stType)
      uiStateFuns += (lazyTypename -> fd)
      fd
    }
    FunctionInvocation(TypedFunDef(uiStateFun, tparams), Seq())
  }

  /**
   * A function for creating a state type for every lazy type. Note that Leon
   * doesn't support 'Any' type yet. So we have to have multiple
   * state (though this is  much clearer it results in more complicated code)
   */
  def getStateType(tname: String, tparams: Seq[TypeParameter]) = {
    //val (_, absdef, _) = tpeToADT(tname)
    SetType(AbstractClassType(closureFactory.absClosureType(tname), tparams))
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
   * Note by using 'assume-pre' we can also assume the preconditions of closures at
   * the call-sites.
   */
  val evalFunctions = tnames.map { tname =>
    val tpe = /*freshenTypeArguments(*/ closureFactory.lazyType(tname) //)
    val absdef = closureFactory.absClosureType(tname)
    val cdefs = closureFactory.closures(tname)

    // construct parameters and return types
    val tparams = getTypeParameters(tpe)
    val tparamDefs = tparams map TypeParameterDef.apply
    val param1 = FreshIdentifier("cl", AbstractClassType(absdef, tparams))
    val stType = getStateType(tname, tparams)
    val param2 = FreshIdentifier("st@", stType)
    val retType = TupleType(Seq(tpe, stType))

    // create a eval function
    val dfun = new FunDef(FreshIdentifier(evalFunctionName(absdef.id.name), Untyped),
      tparamDefs, Seq(ValDef(param1), ValDef(param2)), retType)

    // assign body of the eval fucntion
    // create a match case to switch over the possible class defs and invoke the corresponding functions
    val bodyMatchCases = cdefs map { cdef =>
      val ctype = CaseClassType(cdef, tparams) // we assume that the type parameters of cdefs are same as absdefs
      val binder = FreshIdentifier("t", ctype)
      val pattern = InstanceOfPattern(Some(binder), ctype)
      // create a body of the match
      val args = cdef.fields map { fld => CaseClassSelector(ctype, binder.toVariable, fld.id) }
      val op = closureFactory.caseClassToOp(cdef)
      val targetFun = funMap(op)
      // invoke the target fun with appropriate values
       val invoke = FunctionInvocation(TypedFunDef(targetFun, tparams),
          args ++ (if (funsNeedStates(op)) Seq(param2.toVariable) else Seq()))
       val invokeRes = FreshIdentifier("dres", invoke.getType)
      //println(s"invoking function $targetFun with args $args")
      val (valPart, stPart) = if (funsRetStates(op)) {
        // TODO: here we are assuming that only one state is used, fix this.
       val invokeSt = TupleSelect(invokeRes.toVariable, 2)
        (TupleSelect(invokeRes.toVariable, 1),
            SetUnion(invokeSt, FiniteSet(Set(binder.toVariable), stType.base)))
      } else {
        (invokeRes.toVariable,
            SetUnion(param2.toVariable, FiniteSet(Set(binder.toVariable), stType.base)))
      }
      val rhs = Let(invokeRes, invoke, Tuple(Seq(valPart, stPart)))
      MatchCase(pattern, None, rhs)
    }
    // create a new match case for eager evaluation
    val eagerCase = {
      val eagerDef = closureFactory.eagerClosure(tname)
      val ctype = CaseClassType(eagerDef, tparams)
      val binder = FreshIdentifier("t", ctype)
      // create a body of the match
      val valPart = CaseClassSelector(ctype, binder.toVariable, eagerDef.fields(0).id)
      val rhs = Tuple(Seq(valPart, param2.toVariable)) // state doesn't change for eager closure
      MatchCase(InstanceOfPattern(Some(binder), ctype), None, rhs)
    }
    dfun.body = Some(MatchExpr(param1.toVariable, eagerCase +: bodyMatchCases))
    dfun.addFlag(Annotation("axiom", Seq()))
    (tname -> dfun)
  }.toMap

  /**
   * These are evalFunctions that do not affect the state.
   * TODO: here we can avoid creating two calls to the function one
   * with uninterpreted state and other with input state (since here both are equal)
   */
  val computeFunctions = evalFunctions.map {
    case (tname, evalfd) =>
      val tpe = /*freshenTypeArguments(*/ closureFactory.lazyType(tname) //)
      val param1 = evalfd.params.head
      val fun = new FunDef(FreshIdentifier(evalfd.id.name + "*", Untyped),
        evalfd.tparams, Seq(param1), tpe)
      val uiState = getUninterpretedState(tname, getTypeParameters(tpe))
      val invoke = FunctionInvocation(TypedFunDef(evalfd, evalfd.tparams.map(_.tp)),
        Seq(param1.id.toVariable, uiState))
      fun.body = Some(TupleSelect(invoke, 1))
      (tname -> fun)
  }.toMap

  /**
   * Create closure construction functions that ensures a postcondition.
   * They are defined for each lazy class since it avoids generics and
   * simplifies the type inference (which is not full-fledged in Leon)
   */
  lazy val closureCons = tnames.map { tname =>
    val adt = closureFactory.absClosureType(tname)
    val param1Type = AbstractClassType(adt, adt.tparams.map(_.tp))
    val param1 = FreshIdentifier("cc", param1Type)
    val stType = SetType(param1Type)
    val param2 = FreshIdentifier("st@", stType)
    val tparamDefs = adt.tparams
    val fun = new FunDef(FreshIdentifier(closureConsName(tname)), adt.tparams,
      Seq(ValDef(param1), ValDef(param2)), param1Type)
    fun.body = Some(param1.toVariable)

    // assert that the closure in unevaluated if useRefEquality is enabled
    if (useRefEquality) {
      val resid = FreshIdentifier("res", param1Type)
      val postbody = Not(ElementOfSet(resid.toVariable, param2.toVariable))
      /*SubsetOf(FiniteSet(Set(resid.toVariable), param1Type), param2.toVariable)*/
      fun.postcondition = Some(Lambda(Seq(ValDef(resid)), postbody))
      fun.addFlag(Annotation("axiom", Seq()))
    }
    (tname -> fun)
  }.toMap

  def mapBody(body: Expr): (Map[String, Expr] => Expr, Boolean) = body match {

    case finv @ FunctionInvocation(_, Seq(FunctionInvocation(TypedFunDef(argfd, tparams), args))) // lazy construction ?
    if isLazyInvocation(finv)(p) =>
      val op = (nargs: Seq[Expr]) => ((st: Map[String, Expr]) => {
        val adt = closureFactory.closureOfLazyOp(argfd)
        val cc = CaseClass(CaseClassType(adt, tparams), nargs)
        val baseLazyTypeName = closureFactory.lazyTypeNameOfClosure(adt)
        FunctionInvocation(TypedFunDef(closureCons(baseLazyTypeName), tparams),
          Seq(cc, st(baseLazyTypeName)))
      }, false)
      mapNAryOperator(args, op)

    case finv @ FunctionInvocation(_, Seq(arg)) if isEagerInvocation(finv)(p) =>
      // here arg is guaranteed to be a variable
      ((st: Map[String, Expr]) => {
        val rootType = bestRealType(arg.getType)
        val tname = typeNameWOParams(rootType)
        val tparams = getTypeArguments(rootType)
        val eagerClosure = closureFactory.eagerClosure(tname)
        CaseClass(CaseClassType(eagerClosure, tparams), Seq(arg))
      }, false)

    case finv @ FunctionInvocation(_, args) if isEvaluatedInvocation(finv)(p) => // isEval function ?
      val op = (nargs: Seq[Expr]) => ((st: Map[String, Expr]) => {
        val narg = nargs(0) // there must be only one argument here
        val baseType = unwrapLazyType(narg.getType).get
        val tname = typeNameWOParams(baseType)
        val memberTest = ElementOfSet(narg, st(tname)) // should we use subtype instead ?
        val subtypeTest = IsInstanceOf(narg,
          CaseClassType(closureFactory.eagerClosure(tname), getTypeArguments(baseType)))
        Or(memberTest, subtypeTest)
      }, false)
      mapNAryOperator(args, op)

    case finv @ FunctionInvocation(_, Seq(recvr, funcArg)) if isSuspInvocation(finv)(p) =>
      ((st: Map[String, Expr]) => {
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

    case finv @ FunctionInvocation(_, Seq(recvr, stArg)) if isWithStateFun(finv)(p) =>
      // recvr is a `WithStateCaseClass` and `stArg` could be an arbitrary expression that returns a state
      val CaseClass(_, Seq(exprNeedingState)) = recvr
      val (nexpr, exprReturnsState) = mapBody(exprNeedingState)
      val (nstArg, stArgReturnsState) = mapBody(stArg)
      if(stArgReturnsState)
        throw new IllegalStateException("The state argument to `withState` returns a new state, which is not supported: "+finv)
      else {
        ((st: Map[String, Expr]) => {
          val nst = nstArg(st)
          // compute the baseType
          stArg.getType match {
            case SetType(lazyType) =>
              val baseType = unwrapLazyType(lazyType).get
              val tname = typeNameWOParams(baseType)
              val newStates = st + (tname -> nst)
              nexpr(newStates)
            case t =>
              throw new IllegalStateException(s"$stArg should have a set type, current type: "+t)
          }
        }, exprReturnsState)
      }

    case finv @ FunctionInvocation(_, args) if isValueInvocation(finv)(p) => // is  value function ?
      val op = (nargs: Seq[Expr]) => ((st: Map[String, Expr]) => {
        val baseType = unwrapLazyType(nargs(0).getType).get // there must be only one argument here
        val tname = typeNameWOParams(baseType)
        val dispFun = evalFunctions(tname)
        val dispFunInv = FunctionInvocation(TypedFunDef(dispFun,
          getTypeParameters(baseType)), nargs :+ st(tname))
        val dispRes = FreshIdentifier("dres", dispFun.returnType, true)
        val nstates = tnames map {
          case `tname` =>
            TupleSelect(dispRes.toVariable, 2)
          case other => st(other)
        }
        Let(dispRes, dispFunInv, Tuple(TupleSelect(dispRes.toVariable, 1) +: nstates))
      }, true)
      mapNAryOperator(args, op)

    case finv @ FunctionInvocation(_, args) if isStarInvocation(finv)(p) => // is * function ?
      val op = (nargs: Seq[Expr]) => ((st: Map[String, Expr]) => {
        val baseType = unwrapLazyType(nargs(0).getType).get // there must be only one argument here
        val tname = typeNameWOParams(baseType)
        val dispFun = computeFunctions(tname)
        FunctionInvocation(TypedFunDef(dispFun, getTypeParameters(baseType)), nargs)
      }, false)
      mapNAryOperator(args, op)

    case FunctionInvocation(TypedFunDef(fd, tparams), args) if funMap.contains(fd) =>
      mapNAryOperator(args,
        (nargs: Seq[Expr]) => ((st: Map[String, Expr]) => {
          val stArgs =
            if (funsNeedStates(fd)) {
              (tnames map st.apply)
            } else Seq()
          FunctionInvocation(TypedFunDef(funMap(fd), tparams), nargs ++ stArgs)
        }, funsRetStates(fd)))

    case Let(id, value, body) =>
      val (valCons, valUpdatesState) = mapBody(value)
      val (bodyCons, bodyUpdatesState) = mapBody(body)
      ((st: Map[String, Expr]) => {
        val nval = valCons(st)
        if (valUpdatesState) {
          val freshid = FreshIdentifier(id.name, nval.getType, true)
          val nextStates = tnames.zipWithIndex.map {
            case (tn, i) =>
              TupleSelect(freshid.toVariable, i + 2)
          }.toSeq
          val nsMap = (tnames zip nextStates).toMap
          val transBody = replace(Map(id.toVariable -> TupleSelect(freshid.toVariable, 1)),
            bodyCons(nsMap))
          if (bodyUpdatesState)
            Let(freshid, nval, transBody)
          else
            Let(freshid, nval, Tuple(transBody +: nextStates))
        } else
          Let(id, nval, bodyCons(st))
      }, valUpdatesState || bodyUpdatesState)

    case IfExpr(cond, thn, elze) =>
      val (condCons, condState) = mapBody(cond)
      val (thnCons, thnState) = mapBody(thn)
      val (elzeCons, elzeState) = mapBody(elze)
      ((st: Map[String, Expr]) => {
        val (ncondCons, nst) =
          if (condState) {
            val cndExpr = condCons(st)
            val bder = FreshIdentifier("c", cndExpr.getType)
            val condst = tnames.zipWithIndex.map {
              case (tn, i) => tn -> TupleSelect(bder.toVariable, i + 2)
            }.toMap
            ((th: Expr, el: Expr) =>
              Let(bder, cndExpr, IfExpr(TupleSelect(bder.toVariable, 1), th, el)),
              condst)
          } else {
            ((th: Expr, el: Expr) => IfExpr(condCons(st), th, el), st)
          }
        val nelze =
          if ((condState || thnState) && !elzeState)
            Tuple(elzeCons(nst) +: tnames.map(nst.apply))
          else elzeCons(nst)
        val nthn =
          if (!thnState && (condState || elzeState))
            Tuple(thnCons(nst) +: tnames.map(nst.apply))
          else thnCons(nst)
        ncondCons(nthn, nelze)
      }, condState || thnState || elzeState)

    case MatchExpr(scr, cases) =>
      val (scrCons, scrUpdatesState) = mapBody(scr)
      val casesRes = cases.foldLeft(Seq[(Map[String, Expr] => Expr, Boolean)]()) {
        case (acc, MatchCase(pat, None, rhs)) =>
          acc :+ mapBody(rhs)
        case mcase =>
          throw new IllegalStateException("Match case with guards are not supported yet: " + mcase)
      }
      val casesUpdatesState = casesRes.exists(_._2)
      ((st: Map[String, Expr]) => {
        val scrExpr = scrCons(st)
        val (nscrCons, scrst) = if (scrUpdatesState) {
          val bder = FreshIdentifier("scr", scrExpr.getType)
          val scrst = tnames.zipWithIndex.map {
            case (tn, i) => tn -> TupleSelect(bder.toVariable, i + 2)
          }.toMap
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
                Tuple(caseCons(scrst) +: tnames.map(scrst.apply))
              else caseCons(scrst)
            MatchCase(pat, None, nrhs)
        }
        nscrCons(ncases)
      }, scrUpdatesState || casesUpdatesState)

    // need to reset types in the case of case class constructor calls
    case CaseClass(cct, args) =>
      val ntype = replaceLazyTypes(cct).asInstanceOf[CaseClassType]
      mapNAryOperator(args,
        (nargs: Seq[Expr]) => ((st: Map[String, Expr]) => CaseClass(ntype, nargs), false))

    case Operator(args, op) =>
      // here, 'op' itself does not create a new state
      mapNAryOperator(args,
        (nargs: Seq[Expr]) => ((st: Map[String, Expr]) => op(nargs), false))

    case t: Terminal => (_ => t, false)
  }

  def mapNAryOperator(args: Seq[Expr], op: Seq[Expr] => (Map[String, Expr] => Expr, Boolean)) = {
    // create n variables to model n lets
    val letvars = args.map(arg => FreshIdentifier("arg", arg.getType, true).toVariable)
    (args zip letvars).foldRight(op(letvars)) {
      case ((arg, letvar), (accCons, stUpdatedBefore)) =>
        val (argCons, stUpdateFlag) = mapBody(arg)
        val cl = if (!stUpdateFlag) {
          // here arg does not affect the newstate
          (st: Map[String, Expr]) => replace(Map(letvar -> argCons(st)), accCons(st))
        } else {
          // here arg does affect the newstate
          (st: Map[String, Expr]) =>
            {
              val narg = argCons(st)
              val argres = FreshIdentifier("a", narg.getType, true).toVariable
              val nstateSeq = tnames.zipWithIndex.map {
                // states start from index 2
                case (tn, i) => TupleSelect(argres, i + 2)
              }
              val nstate = (tnames zip nstateSeq).map {
                case (tn, st) => (tn -> st)
              }.toMap[String, Expr]
              val letbody =
                if (stUpdatedBefore) accCons(nstate) // here, 'acc' already returns a superseeding state
                else Tuple(accCons(nstate) +: nstateSeq) // here, 'acc; only retruns the result
              Let(argres.id, narg,
                Let(letvar.id, TupleSelect(argres, 1), letbody))
            }
        }
        (cl, stUpdatedBefore || stUpdateFlag)
    }
  }

  def assignBodiesToFunctions = funMap foreach {
    case (fd, nfd) =>
      //      /println("Considering function: "+fd)
      // Here, using name to identify 'state' parameters, also relying
      // on fact that nfd.params are in the same order as tnames
      val stateParams = nfd.params.foldLeft(Seq[Expr]()) {
        case (acc, ValDef(id, _)) if id.name.startsWith("st@") =>
          acc :+ id.toVariable
        case (acc, _) => acc
      }
      val initStateMap = tnames zip stateParams toMap
      val (nbodyFun, bodyUpdatesState) = mapBody(fd.body.get)
      val nbody = nbodyFun(initStateMap)
      val bodyWithState =
        if (!bodyUpdatesState && funsRetStates(fd)) {
          val freshid = FreshIdentifier("bres", nbody.getType)
          Let(freshid, nbody, Tuple(freshid.toVariable +: stateParams))
        } else nbody
      nfd.body = Some(simplifyLets(bodyWithState))
      //println(s"Body of ${fd.id.name} after conversion&simp:  ${nfd.body}")

      // Important: specifications use lazy semantics but
      // their state changes are ignored after their execution.
      // This guarantees their observational purity/transparency
      // collect class invariants that need to be added
      if (fd.hasPrecondition) {
        val (npreFun, preUpdatesState) = mapBody(fd.precondition.get)
        nfd.precondition =
          if (preUpdatesState)
            Some(TupleSelect(npreFun(initStateMap), 1)) // ignore state updated by pre
          else Some(npreFun(initStateMap))
      }

      // create a new result variable
      val newres =
        if (fd.hasPostcondition) {
          val Lambda(Seq(ValDef(r, _)), _) = fd.postcondition.get
          FreshIdentifier(r.name, bodyWithState.getType)
        } else FreshIdentifier("r", nfd.returnType)

      // create an output state map
      val outStateMap =
        if (bodyUpdatesState || funsRetStates(fd)) {
          tnames.zipWithIndex.map {
            case (tn, i) => (tn -> TupleSelect(newres.toVariable, i + 2))
          }.toMap
        } else
          initStateMap

      // create a specification that relates input-output states
      val stateRel =
        if (funsRetStates(fd)) { // add specs on states
          val instates = initStateMap.values.toSeq
          val outstates = outStateMap.values.toSeq
          val stateRel =
            if(fd.annotations.contains("invstate")) Equals.apply _
            else SubsetOf.apply _
          Some(createAnd((instates zip outstates).map(p => stateRel(p._1, p._2))))
        } else None

      // create a predicate that ensures that the value part is independent of the state
      val valRel =
        if (uiFuncs.contains(fd)) { // add specs on value
          val uipred = uiFuncs(fd)._2
          val args = nfd.params.take(fd.params.size).map(_.id.toVariable)
          val retarg =
            if(funsRetStates(fd))
              TupleSelect(newres.toVariable, 1)
              else newres.toVariable
          Some(FunctionInvocation(TypedFunDef(uipred, nfd.tparams.map(_.tp)),
              args :+ retarg))
        } else None

      val targetPost =
        if (fd.hasPostcondition) {
          val Lambda(Seq(ValDef(resid, _)), post) = fd.postcondition.get
          // bind calls to instate and outstate calls to their respective values
          val tpost = simplePostTransform {
            case e if LazinessUtil.isInStateCall(e)(p) =>
              val baseType = getTypeArguments(e.getType).head
              initStateMap(typeNameWOParams(baseType))

            case e if LazinessUtil.isOutStateCall(e)(p) =>
              val baseType = getTypeArguments(e.getType).head
              outStateMap(typeNameWOParams(baseType))

            case e => e
          }(post)
          // thread state through postcondition
          val (npostFun, postUpdatesState) = mapBody(tpost)
          val resval =
            if (bodyUpdatesState || funsRetStates(fd))
              TupleSelect(newres.toVariable, 1)
            else newres.toVariable
          val npostWithState = replace(Map(resid.toVariable -> resval), npostFun(outStateMap))
          val npost =
            if (postUpdatesState) {
              TupleSelect(npostWithState, 1) // ignore state updated by post
            } else
              npostWithState
          Some(npost)
        } else {
          None
        }
      nfd.postcondition = Some(Lambda(Seq(ValDef(newres)),
          createAnd(stateRel.toList ++ valRel.toList ++ targetPost.toList)))
//      if (removeRecursionViaEval) {
//        uninterpretedTargets.get(fd) match {
//          case Some(uitarget) =>
//            // uitarget uses the same identifiers as nfd
//            uitarget.postcondition = targetPost
//          case None => ;
//        }
//      }
      // add invariants on state
      /*val fpost =
        if (funsRetStates(fd)) { // add specs on states
          val instates = stateParams
          val resid = if (fd.hasPostcondition) {
            val Lambda(Seq(ValDef(r, _)), _) = simpPost.get
            r
          } else FreshIdentifier("r", nfd.returnType)
          val outstates = (0 until tnames.size).map(i => TupleSelect(resid.toVariable, i + 2))
          val invstate = fd.annotations.contains("invstate")
          val statePred = PredicateUtil.createAnd((instates zip outstates).map {
            case (x, y) =>
              if (invstate)
                Equals(x, y)
              else SubsetOf(x, y)
          })
          val post = Lambda(Seq(ValDef(resid)), (if (fd.hasPostcondition) {
            val Lambda(Seq(ValDef(_, _)), p) = simpPost.get
            And(p, statePred)
          } else statePred))
          Some(post)
        } else simpPost*/
      //if (fpost.isDefined) {
        // also attach postcondition to uninterpreted targets
      //}
  }

  def assignContractsForEvals = evalFunctions.foreach {
    case (tname, evalfd) =>
      val cdefs = closureFactory.closures(tname)
      val tparams = evalfd.tparams.map(_.tp)
      val postres = FreshIdentifier("res", evalfd.returnType)
      val postMatchCases = cdefs flatMap { cdef =>
        // create a body of the match (which asserts that return value equals the uninterpreted function)
        val op = closureFactory.lazyopOfClosure(cdef)
        if (uiFuncs.contains(op)) {
          val ctype = CaseClassType(cdef, tparams)
          val binder = FreshIdentifier("t", ctype)
          val pattern = InstanceOfPattern(Some(binder), ctype)
          val args = cdef.fields map { fld => CaseClassSelector(ctype, binder.toVariable, fld.id) }
          val rhs = Equals(TupleSelect(postres.toVariable, 1),
            FunctionInvocation(TypedFunDef(uiFuncs(op)._1, tparams), args)
            )
          Seq(MatchCase(pattern, None, rhs))
        } else Seq()
      }
      // create a default case ot match other cases
      val default = MatchCase(WildcardPattern(None), None, Util.tru)
      evalfd.postcondition = Some(
        Lambda(Seq(ValDef(postres)),
          MatchExpr(evalfd.params.head.toVariable, postMatchCases :+ default)))
  }

  /**
   * Overrides the types of the lazy fields  in the case class definitions
   */
  def transformCaseClasses = p.definedClasses.foreach {
    case ccd @ CaseClassDef(id, tparamDefs, superClass, isCaseObj) =>
      val nfields = ccd.fields.map { fld =>
        unwrapLazyType(fld.getType) match {
          case None => fld
          case Some(btype) =>
            val clType = closureFactory.absClosureType(typeNameWOParams(btype))
            val typeArgs = getTypeArguments(btype)
            //println(s"AbsType: $clType type args: $typeArgs")
            val adtType = AbstractClassType(clType, typeArgs)
            ValDef(fld.id, Some(adtType)) // overriding the field type
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
    addDefs(
      copyProgram(p,
        (defs: Seq[Definition]) => defs.flatMap {
          case fd: FunDef if funMap.contains(fd) =>
            uiFuncs.get(fd) match {
              case Some((funui, predui)) =>
                Seq(funMap(fd), funui, predui)
              case _ => Seq(funMap(fd))
            }
          case d => Seq(d)
        }),
      closureFactory.allClosuresAndParents ++ closureCons.values ++
        evalFunctions.values ++ computeFunctions.values ++ uiStateFuns.values, anchor)
  }
}
