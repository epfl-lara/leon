package leon
package laziness

import invariant.util._
import invariant.structure.FunctionUtils._
import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import HOMemUtil._
import invariant.util.ProgramUtil._
import FreeVariableFactory._

/**
 * Makes sure that the bodies of all the lambdas are function applications
 */
object ExpressionLifter {

  /**
   * convert the argument of every lazy constructors to a procedure
   */
  var globalId = 0
  def freshFunctionNameForClosure = {
    globalId += 1
    "anonFun" + globalId
  }

  /**
   * (a) The functions lifts arguments of '$' to functions
   * (b) lifts eager computations to lazy computations if necessary
   * (c) converts memoization to lazy evaluation
   * (d) Adds unique references to programs that create lazy closures.
   */
  def liftLambdaBody(ctx: LeonContext, prog: Program, createUniqueIds: Boolean = false): Program = {

    val reporter = ctx.reporter

    lazy val funsMan = new FunctionsManager(prog)
    lazy val needsId = funsMan.callersnTargetOfLambdas

    var newfuns = Map[ExprStructure, (FunDef, ModuleDef)]()
    val fdmap = ProgramUtil.userLevelFunctions(prog).collect {
      case fd if fd.hasBody =>
        val nname =
          if (fd.flags.contains(IsField(true)) || hasMemAnnotation(fd)) {
            FreshIdentifier(fd.id.name + "-mem")
          } else
            FreshIdentifier(fd.id.name)
        val nfd =
          if (createUniqueIds && needsId(fd)) {
            val idparam = ValDef(FreshIdentifier("id@", fvType))
            new FunDef(nname, fd.tparams, fd.params :+ idparam, fd.returnType)
          } else
            new FunDef(nname, fd.tparams, fd.params, fd.returnType)
        // remove lazy val/memoized annotations and replace them by a new name
        fd.flags.filterNot(flg => flg == IsField(true) || flg == Annotation("memoize", Seq())).foreach(nfd.addFlag(_))
        (fd -> nfd)
    }.toMap

    var anchorDef: Option[FunDef] = None // a hack to find anchors
    prog.modules.foreach { md =>
      def exprLifter(skipLambda: Boolean)(fl: Option[FreeVarListIterator])(expr: Expr) = expr match {
        case lmb @ Lambda(args, body) if skipLambda =>
          // here, we are within a block where lambdas need not be transformed
          expr
        case lmb @ Lambda(args, body) => // seen a lambda
          body match {
            case FunctionInvocation(tfd, fargs) if fargs.forall(_.isInstanceOf[Terminal]) =>
              lmb.getType match { case FunctionType(argts, rett) =>
                  (rett +: argts).foreach {
                    case t: ClassType if t.parent.isDefined =>
                      reporter.warning(s"Argument or return type of lambda $lmb uses non-root types! This may result in unexpected craches!")
                    case _ =>
                  }
              }
              // here, we lift terminals in arguments outside.
              val (nvars, lcons) = fargs.foldRight((Seq[Variable](), (e: Expr) => e)) {
                case (v: Variable, (nids, lcons)) => (v +: nids, lcons)
                case (t, (nids, lcons)) =>
                  val id = FreshIdentifier("a", t.getType, true)
                  (id.toVariable +: nids,  e => Let(id, t, lcons(e)))
              }
              lcons(Lambda(args, FunctionInvocation(tfd, nvars)))
            case _ =>
              val argvars = args.map(_.id)
              val capturedvars = (variablesOf(body) -- argvars).toList
              val freevars = argvars ++ capturedvars
              val tparams = (freevars.map(_.getType).flatMap(getTypeParameters) ++ {
                collect { // also include all type parameters of case class constants
                  case CaseClass(ctype, _) => getTypeParameters(ctype).toSet
                  case _                   => Set[TypeParameter]()
                }(body)
              }).distinct
              val argstruc = new ExprStructure(body)
              val bodyfun =
                if (newfuns.contains(argstruc)) {
                  newfuns(argstruc)._1
                } else {
                  //construct type parameters for the function
                  val nname = FreshIdentifier(freshFunctionNameForClosure, Untyped, true)
                  val tparamDefs = tparams map TypeParameterDef.apply
                  val params = freevars.map{ fv =>
                    val freshid = FreshIdentifier(fv.name, TypeOps.bestRealType(fv.getType), true)
                    ValDef(freshid)
                  }
                  val retType = TypeOps.bestRealType(body.getType)
                  val nfun =
                    if (createUniqueIds) {
                      val idparam = ValDef(FreshIdentifier("id@", fvType))
                      new FunDef(nname, tparamDefs, params :+ idparam, retType)
                    } else
                      new FunDef(nname, tparamDefs, params, retType)
                  nfun.body = Some(replaceFromIDs((freevars zip params.map(_.id.toVariable)).toMap, body))
                  nfun.addFlag(IsInlined) // add inline annotation to these functions
                  newfuns += (argstruc -> (nfun, md))
                  nfun
                }
              val fvVars = freevars.map(_.toVariable)
              val fargs =
                if (createUniqueIds)
                  fvVars :+ fl.get.nextExpr
                else fvVars
              Lambda(args, FunctionInvocation(TypedFunDef(bodyfun, tparams), fargs))
          }

        // every other function calls
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

          def rec(skipLambda: Boolean)(e: Expr): Expr = e match {
            // skip `fmatch` and `is` function calls
            case finv@FunctionInvocation(tfd, args) if isIsFun(finv)(prog) || isFunMatch(finv)(prog) =>
              FunctionInvocation(tfd, args map rec(true))
            case Operator(args, op) =>
              val nargs = args map rec(skipLambda)
              exprLifter(skipLambda)(fliter)(op(nargs))
          }
          if(fd.hasPrecondition)
            nfd.precondition = Some(rec(false)(fd.precondition.get))
          if (fd.hasPostcondition){
            val Lambda(arg, pbody) = fd.postcondition.get // ignore the lambda of ensuring
            nfd.postcondition = Some(Lambda(arg, rec(false)(pbody)))
          }
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
