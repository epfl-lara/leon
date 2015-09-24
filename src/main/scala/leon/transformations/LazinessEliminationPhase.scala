package leon
package transformations

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
import purescala.FunctionClosure
import scala.collection.mutable.{ Map => MutableMap }
import leon.invariant.util.TypeUtil._
import leon.invariant.util.LetTupleSimplification._
import leon.solvers.TimeoutSolverFactory
import leon.verification.VerificationContext
import leon.verification.DefaultTactic
import leon.verification.AnalysisPhase
import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter
import scala.util.matching.Regex
import leon.purescala.PrettyPrinter

object LazinessEliminationPhase extends TransformationPhase {
  val debug = false
  val dumpProgramWithClosures = false
  val dumpTypeCorrectProg = false
  val dumpFinalProg = false

  // flags
  val removeRecursionViaEval = false
  val skipVerification = false
  val prettyPrint = true
  val optOutputDirectory = new LeonOptionDef[String] {
    val name = "o"
    val description = "Output directory"
    val default = "leon.out"
    val usageRhs = "dir"
    val parser = (x: String) => x
  }

  val name = "Laziness Elimination Phase"
  val description = "Coverts a program that uses lazy construct" +
    " to a program that does not use lazy constructs"

  /**
   * TODO: enforce that the specs do not create lazy closures
   * TODO: we are forced to make an assumption that lazy ops takes as type parameters only those
   * type parameters of their return type and not more. (enforce this)
   * TODO: Check that lazy types are not nested
   */
  def apply(ctx: LeonContext, prog: Program): Program = {

    val nprog = liftLazyExpressions(prog)
    val (tpeToADT, opToAdt) = createClosures(nprog)
    //Override the types of the lazy fields  in the case class definition
    nprog.definedClasses.foreach {
      case ccd @ CaseClassDef(id, tparamDefs, superClass, isCaseObj) =>
        val nfields = ccd.fields.map { fld =>
          unwrapLazyType(fld.getType) match {
            case None => fld
            case Some(btype) =>
              val adtType = AbstractClassType(tpeToADT(typeNameWOParams(btype))._2,
                getTypeParameters(btype))
              ValDef(fld.id, Some(adtType)) // overriding the field type
          }
        }
        ccd.setFields(nfields)
      case _ => ;
    }
    // TODO: for now pick one suitable module. But ideally the lazy closure will be added to a separate module
    // and imported every where
    val progWithClasses = addDefs(nprog,
      tpeToADT.values.flatMap(v => v._2 +: v._3),
      opToAdt.keys.last)
    if (debug)
      println("After adding case class corresponding to lazyops: \n" + ScalaPrinter.apply(progWithClasses))
    val progWithClosures = (new TransformProgramUsingClosures(progWithClasses, tpeToADT, opToAdt))()
    //Rectify type parameters and local types
    val typeCorrectProg = rectifyLocalTypeAndTypeParameters(progWithClosures)
    if (dumpTypeCorrectProg)
      println("After rectifying types: \n" + ScalaPrinter.apply(typeCorrectProg))

    val transProg = assertClosurePres(typeCorrectProg)
    if (dumpFinalProg)
      println("After asserting closure preconditions: \n" + ScalaPrinter.apply(transProg))
    // handle 'axiom annotation
    transProg.definedFunctions.foreach { fd =>
      if (fd.annotations.contains("axiom"))
        fd.addFlag(Annotation("library", Seq()))
    }
    // check specifications (to be moved to a different phase)
    if (!skipVerification)
      checkSpecifications(transProg)
    if (prettyPrint)
      prettyPrintProgramToFile(transProg, ctx)
    transProg
  }

  def prettyPrintProgramToFile(p: Program, ctx: LeonContext) {
    val outputFolder = ctx.findOptionOrDefault(optOutputDirectory)
    try {
      new File(outputFolder).mkdir()
    } catch {
      case _ : java.io.IOException => ctx.reporter.fatalError("Could not create directory " + outputFolder)
    }

    for (u <- p.units if u.isMainUnit) {
      val outputFile = s"$outputFolder${File.separator}${u.id.toString}.scala"
      try {
        val out = new BufferedWriter(new FileWriter(outputFile))
        // remove '@' from the end of the identifier names
        val pat = new Regex("""(\S+)(@)""", "base", "suffix")
        val pgmText = pat.replaceAllIn(PrettyPrinter.apply(p), m => m.group("base"))
        out.write(pgmText)
        out.close()
      }
      catch {
        case _ : java.io.IOException => ctx.reporter.fatalError("Could not write on " + outputFile)
      }
    }
    ctx.reporter.info("Output written on " + outputFolder)
  }

  def isLazyInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.$.apply"
    case _ =>
      false
  }

  def isEvaluatedInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.$.isEvaluated"
    case _ => false
  }

  def isValueInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.$.value"
    case _ => false
  }

  def isStarInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.$.*"
    case _ => false
  }

  def isLazyType(tpe: TypeTree): Boolean = tpe match {
    case CaseClassType(CaseClassDef(cid, _, None, false), Seq(_)) =>
      cid.name == "$"
    case _ => false
  }

  /**
   * TODO: Check that lazy types are not nested
   */
  def unwrapLazyType(tpe: TypeTree) = tpe match {
    case ctype @ CaseClassType(_, Seq(innerType)) if isLazyType(ctype) =>
      Some(innerType)
    case _ => None
  }

  def rootType(t: TypeTree): Option[AbstractClassType] = t match {
    case absT: AbstractClassType => Some(absT)
    case ct: ClassType => ct.parent
    case _ => None
  }

  def opNameToCCName(name: String) = {
    name.capitalize + "@"
  }

  /**
   * Convert the first character to lower case
   * and remove the last character.
   */
  def ccNameToOpName(name: String) = {
    name.substring(0, 1).toLowerCase() +
      name.substring(1, name.length() - 1)
  }

  def typeNameToADTName(name: String) = {
    "Lazy" + name
  }

  def adtNameToTypeName(name: String) = {
    name.substring(4)
  }

  def closureConsName(typeName: String) = {
    "new@" + typeName
  }

  def isClosureCons(fd: FunDef) = {
    fd.id.name.startsWith("new@")
  }

  /**
   * convert the argument of every lazy constructors to a procedure
   */
  def liftLazyExpressions(prog: Program): Program = {
    var newfuns = Map[ExprStructure, (FunDef, ModuleDef)]()
    var anchorFun: Option[FunDef] = None
    val fdmap = prog.modules.flatMap { md =>
      md.definedFunctions.map {
        case fd if fd.hasBody && !fd.isLibrary =>
          //println("FunDef: "+fd)
          val nfd = preMapOnFunDef {
            case finv @ FunctionInvocation(lazytfd, Seq(arg)) if isLazyInvocation(finv)(prog) && !arg.isInstanceOf[FunctionInvocation] =>
              val freevars = variablesOf(arg).toList
              val tparams = freevars.map(_.getType) flatMap getTypeParameters
              val argstruc = new ExprStructure(arg)
              val argfun =
                if (newfuns.contains(argstruc)) {
                  newfuns(argstruc)._1
                } else {
                  //construct type parameters for the function
                  val nfun = new FunDef(FreshIdentifier("lazyarg", arg.getType, true),
                    tparams map TypeParameterDef.apply, arg.getType, freevars.map(ValDef(_)))
                  nfun.body = Some(arg)
                  newfuns += (argstruc -> (nfun, md))
                  nfun
                }
              Some(FunctionInvocation(lazytfd, Seq(FunctionInvocation(TypedFunDef(argfun, tparams),
                freevars.map(_.toVariable)))))
            case _ => None
          }(fd)
          (fd -> Some(nfd))
        case fd => fd -> Some(fd.duplicate)
      }
    }.toMap
    // map  the new functions to themselves
    val newfdMap = newfuns.values.map { case (nfd, _) => nfd -> None }.toMap
    val (repProg, _) = replaceFunDefs(prog)(fdmap ++ newfdMap)
    val nprog =
      if (!newfuns.isEmpty) {
        val modToNewDefs = newfuns.values.groupBy(_._2).map { case (k, v) => (k, v.map(_._1)) }.toMap
        appendDefsToModules(repProg, modToNewDefs)
      } else
        throw new IllegalStateException("Cannot find any lazy computation")
    if (debug)
      println("After lifiting arguments of lazy constructors: \n" + ScalaPrinter.apply(nprog))
    nprog
  }

  /**
   * Create a mapping from types to the lazyops that may produce a value of that type
   * TODO: relax that requirement that type parameters of return type of a function
   * lazy evaluated should include all of its type parameters
   */
  type ClosureData = (TypeTree, AbstractClassDef, Seq[CaseClassDef])
  def createClosures(implicit p: Program) = {
    // collect all the operations that could be lazily evaluated.
    val lazyops = p.definedFunctions.flatMap {
      case fd if (fd.hasBody) =>
        filter(isLazyInvocation)(fd.body.get) map {
          case FunctionInvocation(_, Seq(FunctionInvocation(tfd, _))) => tfd.fd
        }
      case _ => Seq()
    }.distinct
    if (debug) {
      println("Lazy operations found: \n" + lazyops.map(_.id).mkString("\n"))
    }
    val tpeToLazyops = lazyops.groupBy(_.returnType)
    val tpeToAbsClass = tpeToLazyops.map(_._1).map { tpe =>
      val name = typeNameWOParams(tpe)
      val absTParams = getTypeParameters(tpe) map TypeParameterDef.apply
      // using tpe name below to avoid mismatches due to type parameters
      name -> AbstractClassDef(FreshIdentifier(typeNameToADTName(name), Untyped),
        absTParams, None)
    }.toMap
    var opToAdt = Map[FunDef, CaseClassDef]()
    val tpeToADT = tpeToLazyops map {
      case (tpe, ops) =>
        val name = typeNameWOParams(tpe)
        val absClass = tpeToAbsClass(name)
        val absType = AbstractClassType(absClass, absClass.tparams.map(_.tp))
        val absTParams = absClass.tparams
        // create a case class for every operation
        val cdefs = ops map { opfd =>
          assert(opfd.tparams.size == absTParams.size)
          val classid = FreshIdentifier(opNameToCCName(opfd.id.name), Untyped)
          val cdef = CaseClassDef(classid, opfd.tparams, Some(absType), isCaseObject = false)
          val nfields = opfd.params.map { vd =>
            val fldType = vd.getType
            unwrapLazyType(fldType) match {
              case None =>
                ValDef(FreshIdentifier(vd.id.name, fldType))
              case Some(btype) =>
                val adtType = AbstractClassType(absClass, getTypeParameters(btype))
                ValDef(FreshIdentifier(vd.id.name, adtType))
            }
          }
          cdef.setFields(nfields)
          absClass.registerChild(cdef)
          opToAdt += (opfd -> cdef)
          cdef
        }
        (name -> (tpe, absClass, cdefs))
    }
    (tpeToADT, opToAdt)
  }

  /**
   * (a) add state to every function in the program
   * (b) thread state through every expression in the program sequentially
   * (c) replace lazy constructions with case class creations
   * (d) replace isEvaluated with currentState.contains()
   * (e) replace accesses to $.value with calls to dispatch with current state
   */
  class TransformProgramUsingClosures(p: Program,
    tpeToADT: Map[String, ClosureData],
    opToAdt: Map[FunDef, CaseClassDef]) {

    val (funsNeedStates, funsRetStates) = funsNeedingnReturningState(p)
    // fix an ordering on types so that we can instrument programs with their states in the same order
    val tnames = tpeToADT.keys.toSeq
    // create a mapping from functions to new functions
    val funMap = p.definedFunctions.collect {
      case fd if (fd.hasBody && !fd.isLibrary) =>
        // replace lazy types in parameters and return values
        val nparams = fd.params map { vd =>
          ValDef(vd.id, Some(replaceLazyTypes(vd.getType))) // override type of identifier
        }
        val nretType = replaceLazyTypes(fd.returnType)
        // does the function require implicit state ?
        val nfd = if (funsNeedStates(fd)) {
          var newTParams = Seq[TypeParameterDef]()
          val stTypes = tnames map { tn =>
            val absClass = tpeToADT(tn)._2
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
            fd.tparams ++ newTParams, retTypeWithState, nparams ++ stParams)
          // body of these functions are defined later
        } else {
          new FunDef(FreshIdentifier(fd.id.name, Untyped), fd.tparams, nretType, nparams)
        }
        // copy annotations
        fd.flags.foreach(nfd.addFlag(_))
        (fd -> nfd)
    }.toMap

    /**
     * A set of uninterpreted functions that may be used as targets
     * of closures in the eval functions, for efficiency reasons.
     */
    lazy val uninterpretedTargets = {
      funMap.map {
        case (k, v) =>
          val ufd = new FunDef(FreshIdentifier(v.id.name, v.id.getType, true),
            v.tparams, v.returnType, v.params)
          (k -> ufd)
      }.toMap
    }

    /**
     * A function for creating a state type for every lazy type. Note that Leon
     * doesn't support 'Any' type yet. So we have to have multiple
     * state (though this is  much clearer it results in more complicated code)
     */
    def getStateType(tname: String, tparams: Seq[TypeParameter]) = {
      val (_, absdef, _) = tpeToADT(tname)
      SetType(AbstractClassType(absdef, tparams))
    }

    def replaceLazyTypes(t: TypeTree): TypeTree = {
      unwrapLazyType(t) match {
        case None =>
          val NAryType(tps, tcons) = t
          tcons(tps map replaceLazyTypes)
        case Some(btype) =>
          val ntype = AbstractClassType(tpeToADT(
            typeNameWOParams(btype))._2, getTypeParameters(btype))
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
    val adtToOp = opToAdt map { case (k, v) => v -> k }
    val evalFunctions = {
      tpeToADT map {
        case (tname, (tpe, absdef, cdefs)) =>
          val tparams = getTypeParameters(tpe)
          val tparamDefs = tparams map TypeParameterDef.apply
          val param1 = FreshIdentifier("cl", AbstractClassType(absdef, tparams))
          val stType = getStateType(tname, tparams)
          val param2 = FreshIdentifier("st@", stType)
          val retType = TupleType(Seq(tpe, stType))
          val dfun = new FunDef(FreshIdentifier("eval" + absdef.id.name, Untyped),
            tparamDefs, retType, Seq(ValDef(param1), ValDef(param2)))
          // assign body
          // create a match case to switch over the possible class defs and invoke the corresponding functions
          val bodyMatchCases = cdefs map { cdef =>
            val ctype = CaseClassType(cdef, tparams) // we assume that the type parameters of cdefs are same as absdefs
            val binder = FreshIdentifier("t", ctype)
            val pattern = InstanceOfPattern(Some(binder), ctype)
            // create a body of the match
            val args = cdef.fields map { fld => CaseClassSelector(ctype, binder.toVariable, fld.id) }
            val op = adtToOp(cdef)
            val stArgs = // TODO: here we are assuming that only one state is used, fix this.
              if (funsNeedStates(op))
                // Note: it is important to use empty state here to eliminate
                // dependency on state for the result value
                Seq(FiniteSet(Set(), stType.base))
              else Seq()
            val targetFun =
              if (removeRecursionViaEval && op.hasPostcondition) {
                // checking for postcondition is a hack to make sure that we
                // do not make all targets uninterpreted
                uninterpretedTargets(op)
              } else funMap(op)
            val invoke = FunctionInvocation(TypedFunDef(targetFun, tparams), args ++ stArgs) // we assume that the type parameters of lazy ops are same as absdefs
            val invPart = if (funsRetStates(op)) {
              TupleSelect(invoke, 1) // we are only interested in the value
            } else invoke
            val newst = SetUnion(param2.toVariable, FiniteSet(Set(binder.toVariable), stType.base))
            val rhs = Tuple(Seq(invPart, newst))
            MatchCase(pattern, None, rhs)
          }
          dfun.body = Some(MatchExpr(param1.toVariable, bodyMatchCases))
          dfun.addFlag(Annotation("axiom", Seq()))
          (tname -> dfun)
      }
    }

    /**
     * These are evalFunctions that do not affect the state
     */
    val computeFunctions = {
      evalFunctions map {
        case (tname, evalfd) =>
          val (tpe, _, _) = tpeToADT(tname)
          val param1 = evalfd.params.head
          val fun = new FunDef(FreshIdentifier(evalfd.id.name + "*", Untyped),
            evalfd.tparams, tpe, Seq(param1))
          val invoke = FunctionInvocation(TypedFunDef(evalfd, evalfd.tparams.map(_.tp)),
            Seq(param1.id.toVariable, FiniteSet(Set(),
              getStateType(tname, getTypeParameters(tpe)).base)))
          fun.body = Some(TupleSelect(invoke, 1))
          (tname -> fun)
      }
    }

    /**
     * Create closure construction functions that ensures a postcondition.
     * They are defined for each lazy class since it avoids generics and
     * simplifies the type inference (which is not full-fledged in Leon)
     */
    val closureCons = tpeToADT map {
      case (tname, (_, adt, _)) =>
        val param1Type = AbstractClassType(adt, adt.tparams.map(_.tp))
        val param1 = FreshIdentifier("cc", param1Type)
        val stType = SetType(param1Type)
        val param2 = FreshIdentifier("st@", stType)
        val tparamDefs = adt.tparams
        val fun = new FunDef(FreshIdentifier(closureConsName(tname)), adt.tparams, param1Type,
          Seq(ValDef(param1), ValDef(param2)))
        fun.body = Some(param1.toVariable)
        val resid = FreshIdentifier("res", param1Type)
        val postbody = Not(SubsetOf(FiniteSet(Set(resid.toVariable), param1Type), param2.toVariable))
        fun.postcondition = Some(Lambda(Seq(ValDef(resid)), postbody))
        fun.addFlag(Annotation("axiom", Seq()))
        (tname -> fun)
    }

    def mapNAryOperator(args: Seq[Expr], op: Seq[Expr] => (Map[String, Expr] => Expr, Boolean)) = {
      // create n variables to model n lets
      val letvars = args.map(arg => FreshIdentifier("arg", arg.getType, true).toVariable)
      (args zip letvars).foldRight(op(letvars)) {
        case ((arg, letvar), (accCons, stUpdatedBefore)) =>
          val (argCons, stUpdateFlag) = mapBody(arg)
          val cl = if (!stUpdateFlag) {
            // here arg does not affect the newstate
            (st: Map[String, Expr]) => replace(Map(letvar -> argCons(st)), accCons(st)) // here, we don't have to create a let
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

    def mapBody(body: Expr): (Map[String, Expr] => Expr, Boolean) = body match {

      case finv @ FunctionInvocation(_, Seq(FunctionInvocation(TypedFunDef(argfd, tparams), args))) // lazy construction ?
      if isLazyInvocation(finv)(p) =>
        val op = (nargs: Seq[Expr]) => ((st: Map[String, Expr]) => {
          val adt = opToAdt(argfd)
          val cc = CaseClass(CaseClassType(adt, tparams), nargs)
          val baseLazyType = adtNameToTypeName(adt.parent.get.classDef.id.name)
          FunctionInvocation(TypedFunDef(closureCons(baseLazyType), tparams),
            Seq(cc, st(baseLazyType)))
        }, false)
        mapNAryOperator(args, op)

      case finv @ FunctionInvocation(_, args) if isEvaluatedInvocation(finv)(p) => // isEval function ?
        val op = (nargs: Seq[Expr]) => ((st: Map[String, Expr]) => {
          val narg = nargs(0) // there must be only one argument here
          val baseType = unwrapLazyType(narg.getType).get
          val tname = typeNameWOParams(baseType)
          val adtType = AbstractClassType(tpeToADT(tname)._2, getTypeParameters(baseType))
          SubsetOf(FiniteSet(Set(narg), adtType), st(tname))
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

    /**
     * Assign bodies for the functions in funMap.
     */
    def transformFunctions = {
      funMap foreach {
        case (fd, nfd) =>
          //          /println("Considering function: "+fd)
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

          if (fd.hasPostcondition) {
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
              if (postUpdatesState)
                TupleSelect(npost1, 1) // ignore state updated by post
              else npost1
            nfd.postcondition = Some(Lambda(Seq(ValDef(newres)), npost))
          }
      }
    }

    /**
     * Assign specs for the eval functions
     */
    def transformEvals = {
      evalFunctions.foreach {
        case (tname, evalfd) =>
          val cdefs = tpeToADT(tname)._3
          val tparams = evalfd.tparams.map(_.tp)
          val postres = FreshIdentifier("res", evalfd.returnType)
          // create a match case to switch over the possible class defs and invoke the corresponding functions
          val postMatchCases = cdefs map { cdef =>
            val ctype = CaseClassType(cdef, tparams)
            val binder = FreshIdentifier("t", ctype)
            val pattern = InstanceOfPattern(Some(binder), ctype)
            // create a body of the match
            val op = adtToOp(cdef)
            val targetFd = funMap(op)
            val rhs = if (targetFd.hasPostcondition) {
              val args = cdef.fields map { fld => CaseClassSelector(ctype, binder.toVariable, fld.id) }
              val stArgs =
                if (funsNeedStates(op)) // TODO: here we are assuming that only one state is used, fix this.
                  Seq(evalfd.params.last.toVariable)
                else Seq()
              val Lambda(Seq(resarg), targetPost) = targetFd.postcondition.get
              val replaceMap = (targetFd.params.map(_.toVariable) zip (args ++ stArgs)).toMap[Expr, Expr] +
                (resarg.toVariable -> postres.toVariable)
              replace(replaceMap, targetPost)
            } else
              Util.tru
            MatchCase(pattern, None, rhs)
          }
          evalfd.postcondition = Some(
            Lambda(Seq(ValDef(postres)),
              MatchExpr(evalfd.params.head.toVariable, postMatchCases)))
      }
    }

    def apply() = {
      transformFunctions
      transformEvals
      val progWithClosures = addFunDefs(copyProgram(p,
        (defs: Seq[Definition]) => defs.flatMap {
          case fd: FunDef if funMap.contains(fd) =>
            if (removeRecursionViaEval)
              Seq(funMap(fd), uninterpretedTargets(fd))
            else Seq(funMap(fd))
          case d => Seq(d)
        }), closureCons.values ++ evalFunctions.values ++ computeFunctions.values,
        funMap.values.last)
      if (dumpProgramWithClosures)
        println("Program with closures \n" + ScalaPrinter(progWithClosures))
      progWithClosures
    }
  }

  /**
   * Generate lemmas that ensure that preconditions hold for closures.
   */
  def assertClosurePres(p: Program): Program = {

    def hasClassInvariants(cc: CaseClass): Boolean = {
      val opname = ccNameToOpName(cc.ct.classDef.id.name)
      functionByName(opname, p).get.hasPrecondition
    }

    var anchorfd: Option[FunDef] = None
    val lemmas = p.definedFunctions.flatMap {
      case fd if (fd.hasBody && !fd.isLibrary) =>
        //println("collection closure creation preconditions for: "+fd)
        val closures = CollectorWithPaths {
          case FunctionInvocation(TypedFunDef(fund, _),
            Seq(cc: CaseClass, st)) if isClosureCons(fund) && hasClassInvariants(cc) =>
            (cc, st)
        } traverse (fd.body.get) // Note: closures cannot be created in specs
        // Note: once we have separated normal preconditions from state preconditions
        // it suffices to just consider state preconditions here
        closures.map {
          case ((CaseClass(CaseClassType(ccd, _), args), st), path) =>
            anchorfd = Some(fd)
            val target = functionByName(ccNameToOpName(ccd.id.name), p).get //find the target corresponding to the closure
            val pre = target.precondition.get
            val nargs =
              if (target.params.size > args.size) // target takes state ?
                args :+ st
              else args
            val pre2 = replaceFromIDs((target.params.map(_.id) zip nargs).toMap, pre)
            val vc = Implies(And(Util.precOrTrue(fd), path), pre2)
            // create a function for each vc
            val lemmaid = FreshIdentifier(ccd.id.name + fd.id.name + "Lem", Untyped, true)
            val params = variablesOf(vc).toSeq.map(v => ValDef(v))
            val tparams = params.flatMap(p => getTypeParameters(p.getType)).distinct map TypeParameterDef
            val lemmafd = new FunDef(lemmaid, tparams, BooleanType, params)
            lemmafd.body = Some(vc)
            // assert the lemma is true
            val resid = FreshIdentifier("holds", BooleanType)
            lemmafd.postcondition = Some(Lambda(Seq(ValDef(resid)), resid.toVariable))
//            /println("Created lemma function: "+fd)
            lemmafd
        }
      case _ => Seq()
    }
    if (!lemmas.isEmpty)
      addFunDefs(p, lemmas, anchorfd.get)
    else p
  }

  /**
   * Returns all functions that 'need' states to be passed in
   * and those that return a new state.
   * TODO: implement backwards BFS by reversing the graph
   */
  def funsNeedingnReturningState(prog: Program) = {
    val cg = CallGraphUtil.constructCallGraph(prog, false, true)
    var needRoots = Set[FunDef]()
    var retRoots = Set[FunDef]()
    prog.definedFunctions.foreach {
      case fd if fd.hasBody && !fd.isLibrary =>
        postTraversal {
          case finv: FunctionInvocation if isEvaluatedInvocation(finv)(prog) =>
            needRoots += fd
          case finv: FunctionInvocation if isValueInvocation(finv)(prog) =>
            needRoots += fd
            retRoots += fd
          case _ =>
            ;
        }(fd.body.get)
      case _ => ;
    }
    val funsNeedStates = prog.definedFunctions.filterNot(fd =>
      cg.transitiveCallees(fd).toSet.intersect(needRoots).isEmpty).toSet
    val funsRetStates = prog.definedFunctions.filterNot(fd =>
      cg.transitiveCallees(fd).toSet.intersect(retRoots).isEmpty).toSet
    (funsNeedStates, funsRetStates)
  }

  /**
   * This performs a little bit of Hindley-Milner type Inference
   * to correct the local types and also unify type parameters
   */
  def rectifyLocalTypeAndTypeParameters(prog: Program): Program = {
    var typeClasses = new DisjointSets[TypeTree]()
    prog.definedFunctions.foreach {
      case fd if fd.hasBody && !fd.isLibrary =>
        postTraversal {
          case call @ FunctionInvocation(TypedFunDef(fd, tparams), args) =>
            // unify formal type parameters with actual type arguments
            (fd.tparams zip tparams).foreach(x => typeClasses.union(x._1.tp, x._2))
            // unify the type parameters of types of formal parameters with
            // type arguments of actual arguments
            (fd.params zip args).foreach { x =>
              (x._1.getType, x._2.getType) match {
                case (SetType(tf: ClassType), SetType(ta: ClassType)) =>
                  (tf.tps zip ta.tps).foreach { x => typeClasses.union(x._1, x._2) }
                case (tf: TypeParameter, ta: TypeParameter) =>
                  typeClasses.union(tf, ta)
                case _ =>
                  // others could be ignored as they are not part of the state
                  ;
                /*throw new IllegalStateException(s"Types of formal and actual parameters: ($tf, $ta)"
                    + s"do not match for call: $call")*/
              }
            }
          case _ => ;
        }(fd.fullBody)
      case _ => ;
    }

    val equivTPs = typeClasses.toMap
    val fdMap = prog.definedFunctions.collect {
      case fd if !fd.isLibrary => //fd.hasBody &&

        val (tempTPs, otherTPs) = fd.tparams.map(_.tp).partition {
          case tp if tp.id.name.endsWith("@") => true
          case _ => false
        }
        val others = otherTPs.toSet[TypeTree]
        // for each of the type parameter pick one representative from its equvialence class
        val tpMap = fd.tparams.map {
          case TypeParameterDef(tp) =>
            val tpclass = equivTPs.getOrElse(tp, Set(tp))
            val candReps = tpclass.filter(r => others.contains(r) || !r.isInstanceOf[TypeParameter])
            val concRep = candReps.find(!_.isInstanceOf[TypeParameter])
            val rep =
              if (concRep.isDefined) // there exists a concrete type ?
                concRep.get
              else if (!candReps.isEmpty)
                candReps.head
              else
                throw new IllegalStateException(s"Cannot find a non-placeholder in equivalence class $tpclass for fundef: \n $fd")
            tp -> rep
        }.toMap
        val instf = instantiateTypeParameters(tpMap) _
        val paramMap = fd.params.map {
          case vd @ ValDef(id, _) =>
            (id -> FreshIdentifier(id.name, instf(vd.getType)))
        }.toMap
        val ntparams = tpMap.values.toSeq.distinct.collect { case tp: TypeParameter => tp } map TypeParameterDef
        val nfd = new FunDef(fd.id.freshen, ntparams, instf(fd.returnType),
          fd.params.map(vd => ValDef(paramMap(vd.id))))
        fd -> (nfd, tpMap, paramMap)
    }.toMap

    /*
     * Replace fundefs and unify type parameters in function invocations.
     * Replace old parameters by new parameters
     */
    def transformFunBody(ifd: FunDef) = {
      val (nfd, tpMap, paramMap) = fdMap(ifd)
      // need to handle tuple select specially as it breaks if the type of
      // the tupleExpr if it is not TupleTyped.
      // cannot use simplePostTransform because of this
      def rec(e: Expr): Expr = e match {
        case FunctionInvocation(TypedFunDef(callee, targsOld), args) =>
          val targs = targsOld.map {
            case tp: TypeParameter => tpMap.getOrElse(tp, tp)
            case t => t
          }.distinct
          val ncallee =
            if (fdMap.contains(callee))
              fdMap(callee)._1
            else callee
          FunctionInvocation(TypedFunDef(ncallee, targs), args map rec)
        case Variable(id) if paramMap.contains(id) =>
          paramMap(id).toVariable
        case TupleSelect(tup, index) => TupleSelect(rec(tup), index)
        case Operator(args, op) => op(args map rec)
        case t: Terminal => t
      }
      val nbody = rec(ifd.fullBody)
      //println("Inferring types for: "+ifd.id)
      val initGamma = nfd.params.map(vd => vd.id -> vd.getType).toMap
      inferTypesOfLocals(nbody, initGamma)
    }
    copyProgram(prog, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef if fdMap.contains(fd) =>
        val nfd = fdMap(fd)._1
        if (!fd.fullBody.isInstanceOf[NoTree]) {
          nfd.fullBody = simplifyLetsAndLetsWithTuples(transformFunBody(fd))
        }
        fd.flags.foreach(nfd.addFlag(_))
        nfd
      case d => d
    })
  }

  import leon.solvers._
  import leon.solvers.z3._

  def checkSpecifications(prog: Program) {
    val ctx = Main.processOptions(Seq("--solvers=smt-cvc4","--debug=solver"))
    val report = AnalysisPhase.run(ctx)(prog)
    println(report.summaryString)
    /*val timeout = 10
    val rep = ctx.reporter
     * val fun = prog.definedFunctions.find(_.id.name == "firstUnevaluated").get
    // create a verification context.
    val solver = new FairZ3Solver(ctx, prog) with TimeoutSolver
    val solverF = new TimeoutSolverFactory(SolverFactory(() => solver), timeout * 1000)
    val vctx = VerificationContext(ctx, prog, solverF, rep)
    val vc = (new DefaultTactic(vctx)).generatePostconditions(fun)(0)
    val s = solverF.getNewSolver()
    try {
      rep.info(s" - Now considering '${vc.kind}' VC for ${vc.fd.id} @${vc.getPos}...")
      val tStart = System.currentTimeMillis
      s.assertVC(vc)
      val satResult = s.check
      val dt = System.currentTimeMillis - tStart
      val res = satResult match {
        case None =>
          rep.info("Cannot prove or disprove specifications")
        case Some(false) =>
          rep.info("Valid")
        case Some(true) =>
          println("Invalid - counter-example: " + s.getModel)
      }
    } finally {
      s.free()
    }*/
  }

  /**
   * NOT USED CURRENTLY
   * Lift the specifications on functions to the invariants corresponding
   * case classes.
   * Ideally we should class invariants here, but it is not currently supported
   * so we create a functions that can be assume in the pre and post of functions.
   * TODO: can this be optimized
   */
  /*  def liftSpecsToClosures(opToAdt: Map[FunDef, CaseClassDef]) = {
    val invariants = opToAdt.collect {
      case (fd, ccd) if fd.hasPrecondition =>
        val transFun = (args: Seq[Identifier]) => {
          val argmap: Map[Expr, Expr] = (fd.params.map(_.id.toVariable) zip args.map(_.toVariable)).toMap
          replace(argmap, fd.precondition.get)
        }
        (ccd -> transFun)
    }.toMap
    val absTypes = opToAdt.values.collect {
      case cd if cd.parent.isDefined => cd.parent.get.classDef
    }
    val invFuns = absTypes.collect {
      case abs if abs.knownCCDescendents.exists(invariants.contains) =>
        val absType = AbstractClassType(abs, abs.tparams.map(_.tp))
        val param = ValDef(FreshIdentifier("$this", absType))
        val tparams = abs.tparams
        val invfun = new FunDef(FreshIdentifier(abs.id.name + "$Inv", Untyped),
            tparams, BooleanType, Seq(param))
        (abs -> invfun)
    }.toMap
    // assign bodies for the 'invfuns'
    invFuns.foreach {
      case (abs, fd) =>
        val bodyCases = abs.knownCCDescendents.collect {
          case ccd if invariants.contains(ccd) =>
            val ctype = CaseClassType(ccd, fd.tparams.map(_.tp))
            val cvar = FreshIdentifier("t", ctype)
            val fldids = ctype.fields.map {
              case ValDef(fid, Some(fldtpe)) =>
                FreshIdentifier(fid.name, fldtpe)
            }
            val pattern = CaseClassPattern(Some(cvar), ctype,
              fldids.map(fid => WildcardPattern(Some(fid))))
            val rhsInv = invariants(ccd)(fldids)
            // assert the validity of substructures
            val rhsValids = fldids.flatMap {
              case fid if fid.getType.isInstanceOf[ClassType] =>
                val t = fid.getType.asInstanceOf[ClassType]
                val rootDef = t match {
                  case absT: AbstractClassType => absT.classDef
                  case _ if t.parent.isDefined =>
                    t.parent.get.classDef
                }
                if (invFuns.contains(rootDef)) {
                  List(FunctionInvocation(TypedFunDef(invFuns(rootDef), t.tps),
                    Seq(fid.toVariable)))
                } else
                  List()
              case _ => List()
            }
            val rhs = Util.createAnd(rhsInv +: rhsValids)
            MatchCase(pattern, None, rhs)
        }
        // create a default case
        val defCase = MatchCase(WildcardPattern(None), None, Util.tru)
        val matchExpr = MatchExpr(fd.params.head.id.toVariable, bodyCases :+ defCase)
        fd.body = Some(matchExpr)
    }
    invFuns
  }*/
}

