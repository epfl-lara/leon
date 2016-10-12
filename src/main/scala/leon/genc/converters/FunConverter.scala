/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package converters

import purescala.Common._
import purescala.Definitions._
import purescala.Types._
// NOTE don't import CAST._ to decrease possible confusion between the two ASTs

import utils.Position

import ExtraOps._

private[converters] trait FunConverter {
  this: Converters with TypeAnalyser with Builder with MiniReporter =>

  // Extra information about inner functions' context
  // See classes VarInfo and FunCtx and functions convertToFun and
  // FunctionInvocation conversion
  private var funExtraArgss = Map[CAST.Id, Seq[CAST.Id]]()

  // Register extra function argument for the function named `id`
  private def registerFunExtraArgs(id: CAST.Id, params: Seq[CAST.Id]) {
    funExtraArgss = funExtraArgss + ((id, params))
  }

  // Get the extra argument identifiers for the function named `id`
  def getFunExtraArgs(id: CAST.Id) = funExtraArgss.getOrElse(id, Seq())


  // A variable can be locally declared (e.g. function parameter or local variable)
  // or it can be "inherited" from a more global context (e.g. inner functions have
  // access to their outer function parameters).
  case class VarInfo(x: CAST.Var, local: Boolean) {
    // Transform a local variable into a global variable
    def lift = VarInfo(x, false)

    // Generate CAST variable declaration for function signature
    def toParam = CAST.Var(x.id, CAST.Pointer(x.typ))

    // Generate CAST access statement
    def toArg = if (local) CAST.AccessAddr(x.id) else CAST.AccessVar(x.id)
  }

  object FunCtx {
    val empty = FunCtx(Seq())
  }

  case class FunCtx(vars: Seq[VarInfo]) {
    // Transform local variables into "outer" variables
    def lift = FunCtx(vars map { _.lift })

    // Create a new context with more local variables
    def extend(x: CAST.Var): FunCtx = extend(Seq(x))
    def extend(xs: Seq[CAST.Var]): FunCtx = {
      val newVars = xs map { VarInfo(_, true) }
      FunCtx(vars ++ newVars)
    }

    // Check if a given variable's identifier exists in the context and is an "outer" variable
    def hasOuterVar(id: CAST.Id) = vars exists { vi => !vi.local && vi.x.id == id }

    // List all variables' ids
    def extractIds = vars map { _.x.id }

    // Generate arguments for the given identifiers according to the current context
    def toArgs(ids: Seq[CAST.Id]) = {
      val filtered = vars filter { ids contains _.x.id }
      filtered map { _.toArg }
    }

    // Generate parameters (var + type)
    def toParams = vars map { _.toParam }

    // Check whether this context is empy or not
    // i.e. if the function being extracted is a top level one
    def isEmpty = vars.isEmpty
  }

  // Extract inner functions too
  def convertToFun(fd: FunDef)(implicit funCtx: FunCtx): Option[CAST.Fun] = {
    implicit val pos = fd.getPos

    debug(s"Converting function ${fd.id.uniqueName} with annotations: ${fd.annotations}")

    if (!fd.isMain && fd.isExtern && !fd.isManuallyDefined && !fd.isDropped)
      CAST.unsupported("Extern function need to be either manually defined or dropped")

    if (fd.isManuallyDefined && fd.isDropped)
      CAST.unsupported("Function cannot be dropped and manually implemented at the same time")

    if (fd.isDropped) None
    else {
      // Special case: the `main(args)` function is actually just a proxy for `_main()`
      val fun =
        if (fd.isMain) convertToFun_main(fd)
        else           convertToFun_normal(fd)

      registerFun(fun)

      Some(fun)
    }
  }

  private def convertToFun_main(fd: FunDef)(implicit funCtx: FunCtx, pos: Position): CAST.Fun = {
    if (!fd.isExtern)
      CAST.unsupported("It is expected for `main(args)` to be extern")

    // Make sure there is a `_main()` function and has the proper signature
    val uOpt = prog.units find { _ containsDef fd }
    val u = uOpt getOrElse { internalError(s"FunDef comes from an unexpected place") }
    val _mainFdOpt = u.definedFunctions find { _.id.name == "_main" }
    if (_mainFdOpt.isEmpty)
      CAST.unsupported("Please provide a _main() function")

    val _mainFd = _mainFdOpt.get
    if (_mainFd.params.size > 0)
      CAST.unsupported("_main() should not have parameters")

    // TODO Check for main overload and reject the program in such case

    // Artificially create the function (since it is tagged @extern)
    val is_mainIntegral = _mainFd.returnType == Int32Type
    CAST.generateMain(convertToId(_mainFd.id), is_mainIntegral)
  }

  private def convertToFun_normal(fd: FunDef)(implicit funCtx: FunCtx, pos: Position): CAST.Fun = {
    // Forbid return of array as they are allocated on the stack
    if (containsArrayType(fd.returnType))
      CAST.unsupported("Returning arrays")

    // Extract basic information
    val id        = convertToId(fd.id)
    val retType   = convertToType(fd.returnType)
    val stdParams = fd.params map convertToVar

    // Prepend existing variables from the outer function context to
    // this function's parameters
    val extraParams = funCtx.toParams
    val params      = extraParams ++ stdParams

    // Two main cases to handle for body extraction:
    //  - either the function is defined in Scala, or
    //  - the user provided a C code to use instead

    val body = if (fd.isManuallyDefined) {
      if (!funCtx.isEmpty)
        CAST.unsupported(s"Manual implementation cannot be specified for nested functions")

      val manualDef = fd.getManualDefinition

      // Register all the necessary includes
      manualDef.includes foreach { i => registerInclude(CAST.Include(i)) }

      val body = manualDef.code.replaceAllLiterally("__FUNCTION__", id.name)

      Right(body.stripMargin)
    } else {
      // Function Context:
      // 1) Save the variables of the current context for later function invocation
      // 2) Lift & augment funCtx with the current function's arguments
      // 3) Propagate it to the current function's body

      registerFunExtraArgs(id, funCtx.extractIds)

      val funCtx2 = funCtx.lift.extend(stdParams)

      val b    = convertToStmt(fd.fullBody)(funCtx2)
      val body = retType match {
        case CAST.Void => b
        case _         => injectReturn(b)
      }

      Left(body)
    }

    CAST.Fun(id, retType, params, body)
  }

}

