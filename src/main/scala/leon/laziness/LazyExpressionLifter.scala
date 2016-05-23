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
import purescala.TypeOps._
import leon.invariant.util.TypeUtil._
import LazinessUtil._
import invariant.util.ProgramUtil._
import FreeVariableFactory._

object LazyExpressionLifter {

  /**
   * convert the argument of every lazy constructors to a procedure
   */
  var globalId = 0
  def freshFunctionNameForArg = {
    globalId += 1
    "lazyarg" + globalId
  }

  /**
   * (a) The functions lifts arguments of '$' to functions
   * (b) lifts eager computations to lazy computations if necessary
   * (c) converts memoization to lazy evaluation
   * (d) Adds unique references to programs that create lazy closures.
   */
  def liftLazyExpressions(prog: Program, createUniqueIds: Boolean = false): Program = {

    lazy val funsMan = new LazyFunctionsManager(prog)
    lazy val needsId = funsMan.callersnTargetOfLazyCons

    var newfuns = Map[ExprStructure, (FunDef, ModuleDef)]()
    val fdmap = ProgramUtil.userLevelFunctions(prog).collect {
      case fd if fd.hasBody =>
        val nname = FreshIdentifier(fd.id.name)
        val nfd =
          if (createUniqueIds && needsId(fd)) {
            val idparam = ValDef(FreshIdentifier("id@", fvType))
            new FunDef(nname, fd.tparams, fd.params :+ idparam, fd.returnType)
          } else
            new FunDef(nname, fd.tparams, fd.params, fd.returnType)
        fd.flags.foreach(nfd.addFlag(_))
        (fd -> nfd)
    }.toMap

    lazy val lazyFun = ProgramUtil.functionByFullName("leon.lazyeval.$", prog).get
    lazy val valueFun = ProgramUtil.functionByFullName("leon.lazyeval.Lazy.value", prog).get

    var anchorDef: Option[FunDef] = None // a hack to find anchors
    prog.modules.foreach { md =>
      def exprLifter(inmem: Boolean)(fl: Option[FreeVarListIterator])(expr: Expr) = expr match {
        case finv @ FunctionInvocation(lazytfd, Seq(callByNameArg)) if isLazyInvocation(finv)(prog) =>
          val Lambda(Seq(), arg) = callByNameArg // extract the call-by-name parameter
          arg match {
            case _: FunctionInvocation =>
              finv
            case _ =>
              val freevars = variablesOf(arg).toList
              val tparams = freevars.map(_.getType).flatMap(getTypeParameters).distinct
              val argstruc = new ExprStructure(arg)
              val argfun =
                if (newfuns.contains(argstruc)) {
                  newfuns(argstruc)._1
                } else {
                  //construct type parameters for the function
                  // note: we should make the base type of arg as the return type
                  val nname = FreshIdentifier(freshFunctionNameForArg, Untyped, true)
                  val tparamDefs = tparams map TypeParameterDef.apply
                  val params = freevars.map(ValDef(_))
                  val retType = bestRealType(arg.getType)
                  val nfun =
                    if (createUniqueIds) {
                      val idparam = ValDef(FreshIdentifier("id@", fvType))
                      new FunDef(nname, tparamDefs, params :+ idparam, retType)
                    } else
                      new FunDef(nname, tparamDefs, params, retType)
                  nfun.body = Some(arg)
                  newfuns += (argstruc -> (nfun, md))
                  nfun
                }
              val fvVars = freevars.map(_.toVariable)
              val params =
                if (createUniqueIds)
                  fvVars :+ fl.get.nextExpr
                else fvVars
              FunctionInvocation(lazytfd, Seq(Lambda(Seq(),
                FunctionInvocation(TypedFunDef(argfun, tparams), params))))
          }

        // is the argument of eager invocation not a variable ?
        case finv @ FunctionInvocation(TypedFunDef(fd, Seq(tp)), cbn @ Seq(Lambda(Seq(), arg))) if isEagerInvocation(finv)(prog) =>
          val rootType = bestRealType(tp)
          val ntps = Seq(rootType)
          arg match {
            case _: Variable =>
              FunctionInvocation(TypedFunDef(fd, ntps), cbn)
            case _ =>
              val freshid = FreshIdentifier("t", rootType)
              Let(freshid, arg, FunctionInvocation(TypedFunDef(fd, ntps),
                Seq(Lambda(Seq(), freshid.toVariable))))
          }

        // is this an invocation of a memoized  function ?
        case FunctionInvocation(TypedFunDef(fd, targs), args) if isMemoized(fd) && !inmem =>
          // calling a memoized function is modeled as creating a lazy closure and forcing it
          val tfd = TypedFunDef(fdmap.getOrElse(fd, fd), targs)
          val finv = FunctionInvocation(tfd, args)
          // enclose the call within the $ and force it
          val susp = FunctionInvocation(TypedFunDef(lazyFun, Seq(tfd.returnType)), Seq(Lambda(Seq(), finv)))
          FunctionInvocation(TypedFunDef(valueFun, Seq(tfd.returnType)), Seq(susp))

        // every other function calls ?
        case FunctionInvocation(TypedFunDef(fd, targs), args) if fdmap.contains(fd) =>
          val nargs =
            if (createUniqueIds && needsId(fd))
              args :+ fl.get.nextExpr
            else args
          FunctionInvocation(TypedFunDef(fdmap(fd), targs), nargs)

        case e => e
      }
      md.definedFunctions.foreach {
        case fd if fd.hasBody && !fd.isLibrary && !fd.isInvariant =>
          // create a free list iterator
          val nfd = fdmap(fd)
          val fliter =
            if (createUniqueIds && needsId(fd)) {
              if (!anchorDef.isDefined)
                anchorDef = Some(nfd)
              val initRef = nfd.params.last.id.toVariable
              Some(getFreeListIterator(initRef))
            } else
              None

          def rec(inmem: Boolean)(e: Expr): Expr = e match {
            case Operator(args, op) =>
              val nargs = args map rec(inmem || isMemCons(e)(prog))
              exprLifter(inmem)(fliter)(op(nargs))
          }
          if(fd.hasPrecondition)
            nfd.precondition = Some(rec(true)(fd.precondition.get))
          if (fd.hasPostcondition)
            nfd.postcondition = Some(rec(true)(fd.postcondition.get))
          nfd.body = Some(rec(false)(fd.body.get))
        case fd =>
      }
    }
    val progWithFuns = copyProgram(prog, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef => fdmap.getOrElse(fd, fd)
      case d          => d
    })
    val progWithClasses =
      if (createUniqueIds) ProgramUtil.addDefs(progWithFuns, fvClasses, anchorDef.get)
      else progWithFuns
    if (!newfuns.isEmpty) {
      val modToNewDefs = newfuns.values.groupBy(_._2).map { case (k, v) => (k, v.map(_._1)) }.toMap
      appendDefsToModules(progWithClasses, modToNewDefs)
    } else
      progWithClasses
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
  // Expressions for testing solvers
  // a test expression
  /*val tparam =
    val dummyFunDef = new FunDef(FreshIdentifier("i"),Seq(), Seq(), IntegerType)
    val eq = Equals(FunctionInvocation(TypedFunDef(dummyFunDef, Seq()), Seq()), InfiniteIntegerLiteral(0))
    import solvers._
    val solver = SimpleSolverAPI(SolverFactory(() => new solvers.smtlib.SMTLIBCVC4Solver(ctx, prog)))
    solver.solveSAT(eq) match {
      case (Some(true), m) =>
        println("Model: "+m.toMap)
      case _ => println("Formula is unsat")
    }
    System.exit(0)*/
}
