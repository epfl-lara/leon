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
import invariant.util.ProgramUtil._
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
  val removeRecursionViaEval = false
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

  /**
   * A set of uninterpreted functions that may be used as targets
   * of closures in the eval functions, for efficiency reasons.
   */
  lazy val uninterpretedTargets = funMap.collect {
    case (k, v) if closureFactory.isLazyOp(k) =>
      val ufd = new FunDef(FreshIdentifier(v.id.name, v.id.getType, true),
        v.tparams, v.params, v.returnType)
      (k -> ufd)
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
      val targetFun =
        if (removeRecursionViaEval && op.hasPostcondition) {
          // checking for postcondition is a hack to make sure that we
          // do not make all targets uninterpreted
          uninterpretedTargets(op)
        } else funMap(op)
      // TODO: here we are assuming that only one state is used, fix this.

      //(a) construct the value component
      val stArgs =
        if (funsNeedStates(op)) {
          // Note: it is important to use uninterpreted state here for 2 reasons:
          // (a) to eliminate dependency on state for the result value
          // (b) to avoid inconsistencies when using a fixed state such as empty state
          Seq(getUninterpretedState(tname, tparams))
        } else Seq()
      //println(s"invoking function $targetFun with args $args")
      val invoke = FunctionInvocation(TypedFunDef(targetFun, tparams), args ++ stArgs) // we assume that the type parameters of lazy ops are same as absdefs
      val invPart = if (funsRetStates(op)) {
        TupleSelect(invoke, 1) // we are only interested in the value
      } else invoke

      //(b) construct the state component
      val stPart = if (funsRetStates(op)) {
        val stInvoke = FunctionInvocation(TypedFunDef(targetFun, tparams),
          args ++ (if (funsNeedStates(op)) Seq(param2.toVariable) else Seq()))
        TupleSelect(stInvoke, 2)
      } else param2.toVariable
      val newst = SetUnion(stPart, FiniteSet(Set(binder.toVariable), stType.base))
      val rhs = Tuple(Seq(invPart, newst))
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

    case finv @ FunctionInvocation(_, args) if isValueInvocation(finv)(p) => // is  value function ?
      val op = (nargs: Seq[Expr]) => ((st: Map[String, Expr]) => {
        val baseType = unwrapLazyType(nargs(0).getType).get // there must be only one argument here
        val tname = typeNameWOParams(baseType)
        val dispFun = evalFunctions(tname)
        val dispFunInv = FunctionInvocation(TypedFunDef(dispFun,
          getTypeParameters(baseType)), nargs :+ st(tname))
        val dispRes = FreshIdentifier("dres", dispFun.returnType)
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

      val simpPost = if (fd.hasPostcondition) {
        val Lambda(arg @ Seq(ValDef(resid, _)), post) = fd.postcondition.get
        val (npostFun, postUpdatesState) = mapBody(post)
        val newres = FreshIdentifier(resid.name, bodyWithState.getType)
        val npost1 =
          if (bodyUpdatesState || funsRetStates(fd)) {
            val stmap = tnames.zipWithIndex.map {
              case (tn, i) => (tn -> TupleSelect(newres.toVariable, i + 2))
            }.toMap
            replace(Map(resid.toVariable -> TupleSelect(newres.toVariable, 1)), npostFun(stmap))
          } else
            replace(Map(resid.toVariable -> newres.toVariable), npostFun(initStateMap))
        val npost =
          if (postUpdatesState) {
            TupleSelect(npost1, 1) // ignore state updated by post
          } else npost1
        Some(Lambda(Seq(ValDef(newres)), npost))
      } else None
      // add invariants on state
      val fpost =
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
        } else simpPost
      if (fpost.isDefined) {
        nfd.postcondition = fpost
        // also attach postcondition to uninterpreted targets
        if (removeRecursionViaEval) {
          uninterpretedTargets.get(fd) match {
            case Some(uitarget) =>
              /*val nfdRes = fpost.get.args(0).id
              val repmap: Map[Expr, Expr] = ((nfdRes.toVariable, FreshIdentifier(nfdRes.name).toVariable) +:
                (nfd.params.map(_.id.toVariable) zip uitarget.params.map(_.id.toVariable))).toMap*/
              // uitarget uses the same identifiers as nfd
              uitarget.postcondition = fpost
            case None => ;
          }
        }
      }
  }

  /**
   * This method is not used for now,
   */
  def assignContractsForEvals = evalFunctions.foreach {
    case (tname, evalfd) =>
      val cdefs = closureFactory.closures(tname)
      val tparams = evalfd.tparams.map(_.tp)
      val postres = FreshIdentifier("res", evalfd.returnType)
      val postMatchCases = cdefs map { cdef =>
        val ctype = CaseClassType(cdef, tparams)
        val binder = FreshIdentifier("t", ctype)
        val pattern = InstanceOfPattern(Some(binder), ctype)
        // create a body of the match
        val op = closureFactory.lazyopOfClosure(cdef)
        val targetFd = funMap(op)
        val rhs = if (targetFd.hasPostcondition) {
          val Lambda(Seq(resparam), targetPost) = targetFd.postcondition.get
          val args = cdef.fields map { fld => CaseClassSelector(ctype, binder.toVariable, fld.id) }
          val stArgs =
            if (funsNeedStates(op)) // TODO: here we are assuming that only one state is used, fix this.
              Seq(evalfd.params.last.toVariable)
            else Seq()
          val resarg =
            if (funsRetStates(op))
              postres.toVariable
            else
              TupleSelect(postres.toVariable, 1) // here 'targetFd' does not return state, but eval does
          val replaceMap = (targetFd.params.map(_.toVariable) zip (args ++ stArgs)).toMap[Expr, Expr] +
            (resparam.toVariable -> resarg)
          replace(replaceMap, targetPost)
        } else
          Util.tru
        MatchCase(pattern, None, rhs)
      }
      // create a default case to match eagerClosures
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
    //assignContractsForEvals
    addDefs(
      copyProgram(p,
        (defs: Seq[Definition]) => defs.flatMap {
          case fd: FunDef if funMap.contains(fd) =>
            if (removeRecursionViaEval) {
              uninterpretedTargets.get(fd) match {
                case Some(uitarget) =>
                  Seq(funMap(fd), uitarget)
                case _ => Seq(funMap(fd))
              }
            } else Seq(funMap(fd))
          case d => Seq(d)
        }),
      closureFactory.allClosuresAndParents ++ closureCons.values ++
        evalFunctions.values ++ computeFunctions.values ++ uiStateFuns.values, anchor)
  }
}
