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
import  invariant.structure.FunctionUtils._
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
        // copy the decreases measure
        nfd.decreaseMeasure = fd.decreaseMeasure
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
            case finv @ FunctionInvocation(tfd, args) if isIsFun(finv) || isFunMatch(finv) =>
              FunctionInvocation(tfd, args map rec(true))
            // skip lambdas in the `tmpl` fun invocations
            case fi @ FunctionInvocation(tfd, Seq(Lambda(args, body))) if isTemplateInvocation(fi) =>
              FunctionInvocation(tfd, Seq(Lambda(args, rec(skipLambda)(body))))
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
}
