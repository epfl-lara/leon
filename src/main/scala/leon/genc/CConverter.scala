/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Types._
import xlang.Expressions._

import scala.reflect.ClassTag

// don't import CAST._ to decrease possible confusion between the two ASTs

class CConverter(val ctx: LeonContext, val prog: Program) {
  def convert: CAST.Prog = convertToProg(prog)

  // Global data: keep track of the custom types and function of the input program
  // Using sequences and not sets to keep track of order/dependencies
  private var typeDecls = Seq[CAST.Struct]()
  private var functions = Seq[CAST.Fun]()

  // Extra information about inner functions' context
  // See classes VarInfo and FunCtx and functions convertToFun and
  // FunctionInvocation conversion
  private var funExtraArgss = Map[CAST.Id, Seq[CAST.Id]]()
  private val emptyFunCtx   = FunCtx(Seq())

  private def registerType(typ: CAST.Struct) {
    // Types might be processed more than once as the corresponding CAST type
    // is not cached and need to be reconstructed several time if necessary
    if (!typeDecls.contains(typ)) {
      typeDecls = typeDecls :+ typ
      debug(s"New type registered: $typ")
    }
  }

  private def registerFun(fun: CAST.Fun) {
    // Unlike types, functions should not get defined multiple times as this
    // would imply invalidating funExtraArgss
    if (functions contains fun)
      internalError("Function ${fun.id} defined more than once")
    else
      functions = functions :+ fun
  }

  // Register extra function argument for the function named `id`
  private def registerFunExtraArgs(id: CAST.Id, params: Seq[CAST.Id]) {
    funExtraArgss = funExtraArgss + ((id, params))
  }

  // Get the extra argument identifiers for the function named `id`
  private def getFunExtraArgs(id: CAST.Id) = funExtraArgss.getOrElse(id, Seq())

  // Apply the conversion function and make sure the resulting AST matches our expectation
  private def convertTo[T](tree: Tree)(implicit funCtx: FunCtx, ct: ClassTag[T]): T = convert(tree) match {
    case t: T => t
    case x    => internalError(s"Expected an instance of $ct when converting $tree but got $x")
  }

  // Generic conversion function
  // Currently simple aliases in case we need later to have special treatment instead
  private def convertToType  (tree: Tree)(implicit funCtx: FunCtx) = convertTo[CAST.Type](tree)
  private def convertToStruct(tree: Tree)(implicit funCtx: FunCtx) = convertTo[CAST.Struct](tree)
  private def convertToId    (tree: Tree)(implicit funCtx: FunCtx) = convertTo[CAST.Id](tree)
  private def convertToStmt  (tree: Tree)(implicit funCtx: FunCtx) = convertTo[CAST.Stmt](tree)
  private def convertToVar   (tree: Tree)(implicit funCtx: FunCtx) = convertTo[CAST.Var](tree)

  private def convertToProg(prog: Program): CAST.Prog = {
    // Only process the main unit
    val (mainUnits, _) = prog.units partition { _.isMainUnit }

    if (mainUnits.size == 0) fatalError("No main unit in the program")
    if (mainUnits.size >= 2) fatalError("Multiple main units in the program")

    val mainUnit = mainUnits.head

    debug(s"Converting the main unit:\n$mainUnit")
    collectSymbols(mainUnit)

    CAST.Prog(typeDecls, functions)
  }

  // Look for function and structure definitions
  private def collectSymbols(unit: UnitDef) {
    implicit val defaultFunCtx = emptyFunCtx

    unit.defs.foreach {
      case ModuleDef(_, funDefs, _) =>
        funDefs.foreach {
          case fd: FunDef       => convertToFun(fd)    // the function gets registered here
          case cc: CaseClassDef => convertToStruct(cc) // the type declaration gets registered here

          case x => internalError(s"Unknown function definition $x: ${x.getClass}")
        }

      case x => internalError(s"Unexpected definition $x instead of a ModuleDef")
    }
  }

  // A variable can be locally declared (e.g. function parameter or local variable)
  // or it can be "inherited" from a more global context (e.g. inner functions have
  // access to their outer function parameters).
  private case class VarInfo(x: CAST.Var, local: Boolean) {
    // Transform a local variable into a global variable
    def lift = VarInfo(x, false)

    // Generate CAST variable declaration for function signature
    def toParam = CAST.Var(x.id, CAST.Pointer(x.typ))

    // Generate CAST access statement
    def toArg = if (local) CAST.AccessAddr(x.id) else CAST.AccessVar(x.id)
  }

  private case class FunCtx(vars: Seq[VarInfo]) {
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
  }

  // Extract inner functions too
  private def convertToFun(fd: FunDef)(implicit funCtx: FunCtx) = {
    // Forbid return of array as they are allocated on the stack
    if (containsArrayType(fd.returnType)) {
      fatalError("Returning arrays is currently not allowed")
    }

    val id        = convertToId(fd.id)
    val retType   = convertToType(fd.returnType)
    val stdParams = fd.params map convertToVar

    // Prepend existing variables from the outer function context to
    // this function's parameters
    val extraParams = funCtx.toParams
    val params      = extraParams ++ stdParams

    // Function LeonContext:
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

    val fun = CAST.Fun(id, retType, params, body)
    registerFun(fun)

    fun
  }

  private def convert(tree: Tree)(implicit funCtx: FunCtx): CAST.Tree = tree match {
    /* ---------------------------------------------------------- Types ----- */
    case Int32Type   => CAST.Int32
    case BooleanType => CAST.Bool
    case UnitType    => CAST.Void

    case ArrayType(base) =>
      val typ = CAST.Array(convertToType(base))
      registerType(typ)
      typ

    case TupleType(bases) =>
      val typ = CAST.Tuple(bases map convertToType)
      registerType(typ)
      typ

    case cd: CaseClassDef =>
      if (cd.isAbstract)         fatalError("Abstract types are not supported")
      if (cd.hasParent)          fatalError("Inheritance is not supported")
      if (cd.isCaseObject)       fatalError("Case Objects are not supported")
      if (cd.tparams.length > 0) fatalError("Type Parameters are not supported")
      if (cd.methods.length > 0) fatalError("Methods are not yet supported")

      val id     = convertToId(cd.id)
      val fields = cd.fields map convertToVar
      val typ    = CAST.Struct(id, fields)

      registerType(typ)
      typ

    case CaseClassType(cd, _) => convertToStruct(cd) // reuse `case CaseClassDef`

    /* ------------------------------------------------------- Literals ----- */
    case IntLiteral(v)     => CAST.IntLiteral(v)
    case BooleanLiteral(b) => CAST.BoolLiteral(b)
    case UnitLiteral()     => CAST.NoStmt

    /* ------------------------------------ Definitions and Statements  ----- */
    case id: Identifier =>
      if (id.name == "main") CAST.Id("main") // and not `main0`
      else                   CAST.Id(id.uniqueName)

    // Function parameter
    case vd: ValDef  => buildVal(vd.id, vd.getType)

    // Accessing variable
    case v: Variable => buildAccessVar(v.id)

    case Block(exprs, last) =>
      // Interleave the "bodies" of flatten expressions and their values
      // and generate a Compound statement
      (exprs :+ last) map convertToStmt reduce { _ ~ _ }

    case Let(b, v, r)    => buildLet(b, v, r, false)
    case LetVar(b, v, r) => buildLet(b, v, r, true)

    case LetDef(fds, rest) =>
      fds foreach convertToFun // The functions get registered there
      convertToStmt(rest)

    case Assignment(varId, expr) =>
      val f = convertAndFlatten(expr)
      val x = buildAccessVar(varId)

      val assign = CAST.Assign(x, f.value)

      f.body ~~ assign

    case tuple @ Tuple(exprs) =>
      val struct = convertToStruct(tuple.getType)
      val types  = struct.fields map { _.typ }
      val fs     = convertAndNormaliseExecution(exprs, types)
      val args   = fs.values.zipWithIndex map {
        case (arg, idx) => (CAST.Tuple.getNthId(idx + 1), arg)
      }

      fs.bodies ~~ CAST.StructInit(args, struct)

    case TupleSelect(tuple1, idx) => // here idx is already 1-based
      val struct = convertToStruct(tuple1.getType)
      val tuple2 = convertToStmt(tuple1)

      val fs = normaliseExecution((tuple2, struct) :: Nil)

      val tuple = fs.values.head

      fs.bodies ~~ CAST.AccessField(tuple, CAST.Tuple.getNthId(idx))

    case ArrayLength(array1) =>
      val array2    = convertToStmt(array1)
      val arrayType = convertToType(array1.getType)

      val fs = normaliseExecution((array2, arrayType) :: Nil)

      val array = fs.values.head

      fs.bodies ~~ CAST.AccessField(array, CAST.Array.lengthId)

    case ArraySelect(array1, index1) =>
      val array2    = convertToStmt(array1)
      val arrayType = convertToType(array1.getType)
      val index2    = convertToStmt(index1)

      val fs = normaliseExecution((array2, arrayType) :: (index2, CAST.Int32) :: Nil)

      val array  = fs.values(0)
      val index  = fs.values(1)
      val ptr    = CAST.AccessField(array, CAST.Array.dataId)
      val select = CAST.SubscriptOp(ptr, index)

      fs.bodies ~~ select

    case NonemptyArray(elems, Some((value1, length1))) if elems.isEmpty =>
      val length2   = convertToStmt(length1)
      val valueType = convertToType(value1.getType)
      val value2    = convertToStmt(value1)

      val fs = normaliseExecution((length2, CAST.Int32) :: (value2, valueType) :: Nil)
      val length = fs.values(0)
      val value  = fs.values(1)

      fs.bodies ~~ CAST.ArrayInit(length, valueType, value)

    case NonemptyArray(elems, Some(_)) =>
      fatalError("NonemptyArray with non empty elements is not supported")

    case NonemptyArray(elems, None) => // Here elems is non-empty
      // Sort values according the the key (aka index)
      val indexes = elems.keySet.toSeq.sorted
      val values  = indexes map { elems(_) }

      // Assert all types are the same
      val types   = values map { e => convertToType(e.getType) }
      val typ     = types(0)
      val allSame = types forall { _ == typ }
      if (!allSame) fatalError("Heterogenous arrays are not supported")

      val fs = convertAndNormaliseExecution(values, types)

      fs.bodies ~~ CAST.ArrayInitWithValues(typ, fs.values)

    case ArrayUpdate(array1, index1, newValue1) =>
      val array2    = convertToStmt(array1)
      val index2    = convertToStmt(index1)
      val newValue2 = convertToStmt(newValue1)
      val values    = array2    :: index2    :: newValue2 :: Nil

      val arePure   = values forall { _.isPure }
      val areValues = array2.isValue && index2.isValue // no newValue here

      newValue2 match {
        case CAST.IfElse(cond, thn, elze) if arePure && areValues =>
          val array  = array2
          val index  = index2
          val ptr    = CAST.AccessField(array, CAST.Array.dataId)
          val select = CAST.SubscriptOp(ptr, index)

          val ifelse = buildIfElse(cond, injectAssign(select, thn),
                                         injectAssign(select, elze))

          ifelse

        case _ =>
          val arrayType = convertToType(array1.getType)
          val indexType = CAST.Int32
          val valueType = convertToType(newValue1.getType)
          val types     = arrayType :: indexType :: valueType :: Nil

          val fs = normaliseExecution(values, types)

          val array    = fs.values(0)
          val index    = fs.values(1)
          val newValue = fs.values(2)

          val ptr    = CAST.AccessField(array, CAST.Array.dataId)
          val select = CAST.SubscriptOp(ptr, index)
          val assign = CAST.Assign(select, newValue)

          fs.bodies ~~ assign
      }

    case CaseClass(typ, args1) =>
      val struct    = convertToStruct(typ)
      val types     = struct.fields map { _.typ }
      val argsFs    = convertAndNormaliseExecution(args1, types)
      val fieldsIds = typ.classDef.fieldsIds map convertToId
      val args      = fieldsIds zip argsFs.values

      argsFs.bodies ~~ CAST.StructInit(args, struct)

    case CaseClassSelector(_, x1, fieldId) =>
      val struct = convertToStruct(x1.getType)
      val x2     = convertToStmt(x1)

      val fs = normaliseExecution((x2, struct) :: Nil)
      val x  = fs.values.head

      fs.bodies ~~ CAST.AccessField(x, convertToId(fieldId))

    case LessThan(lhs, rhs)       => buildBinOp(lhs, "<",   rhs)
    case GreaterThan(lhs, rhs)    => buildBinOp(lhs, ">",   rhs)
    case LessEquals(lhs, rhs)     => buildBinOp(lhs, "<=",  rhs)
    case GreaterEquals(lhs, rhs)  => buildBinOp(lhs, ">=",  rhs)
    case Equals(lhs, rhs)         => buildBinOp(lhs, "==",  rhs)

    case Not(rhs)                 => buildUnOp (     "!",   rhs)

    case And(exprs)               => buildMultiOp("&&", exprs)
    case Or(exprs)                => buildMultiOp("||", exprs)

    case BVPlus(lhs, rhs)         => buildBinOp(lhs, "+",   rhs)
    case BVMinus(lhs, rhs)        => buildBinOp(lhs, "-",   rhs)
    case BVUMinus(rhs)            => buildUnOp (     "-",   rhs)
    case BVTimes(lhs, rhs)        => buildBinOp(lhs, "*",   rhs)
    case BVDivision(lhs, rhs)     => buildBinOp(lhs, "/",   rhs)
    case BVRemainder(lhs, rhs)    => buildBinOp(lhs, "%",   rhs)
    case BVNot(rhs)               => buildUnOp (     "~",   rhs)
    case BVAnd(lhs, rhs)          => buildBinOp(lhs, "&",   rhs)
    case BVOr(lhs, rhs)           => buildBinOp(lhs, "|",   rhs)
    case BVXOr(lhs, rhs)          => buildBinOp(lhs, "^",   rhs)
    case BVShiftLeft(lhs, rhs)    => buildBinOp(lhs, "<<",  rhs)
    case BVAShiftRight(lhs, rhs)  => buildBinOp(lhs, ">>", rhs)
    case BVLShiftRight(lhs, rhs)  => fatalError("operator >>> not supported")

    // Ignore assertions for now
    case Ensuring(body, _)  => convert(body)
    case Require(_, body)   => convert(body)
    case Assert(_, _, body) => convert(body)

    case IfExpr(cond1, thn1, elze1) =>
      val condF = convertAndFlatten(cond1)
      val thn   = convertToStmt(thn1)
      val elze  = convertToStmt(elze1)

      condF.body ~~ buildIfElse(condF.value, thn, elze)

    case While(cond1, body1) =>
      val cond = convertToStmt(cond1)
      val body = convertToStmt(body1)

      if (cond.isPureValue) {
        CAST.While(cond, body)
      } else {
        // Transform while (cond) { body } into
        // while (true) { if (cond) { body } else { break } }
        val condF = flatten(cond)
        val ifelse  = condF.body ~~ buildIfElse(condF.value, CAST.NoStmt, CAST.Break)
        CAST.While(CAST.True, ifelse ~ body)
      }

    case FunctionInvocation(tfd @ TypedFunDef(fd, _), stdArgs) =>
      // In addition to regular function parameters, add the callee's extra parameters
      val id        = convertToId(fd.id)
      val types     = tfd.params map { p => convertToType(p.getType) }
      val fs        = convertAndNormaliseExecution(stdArgs, types)
      val extraArgs = funCtx.toArgs(getFunExtraArgs(id))
      val args      = extraArgs ++ fs.values

      fs.bodies ~~ CAST.Call(id, args)

    case unsupported =>
      fatalError(s"$unsupported (of type ${unsupported.getClass}) is currently not supported by GenC")
  }

  private def buildVar(id: Identifier, typ: TypeTree)(implicit funCtx: FunCtx) =
    CAST.Var(convertToId(id), convertToType(typ))

  private def buildVal(id: Identifier, typ: TypeTree)(implicit funCtx: FunCtx) =
    CAST.Val(convertToId(id), convertToType(typ))

  private def buildAccessVar(id1: Identifier)(implicit funCtx: FunCtx) = {
    // Depending on the context, we have to deference the variable
    val id = convertToId(id1)
    if (funCtx.hasOuterVar(id)) CAST.AccessRef(id)
    else                        CAST.AccessVar(id)
  }

  private def buildLet(id: Identifier, value: Expr, rest1: Expr, forceVar: Boolean)
                      (implicit funCtx: FunCtx): CAST.Stmt = {
    val (x, stmt) = buildDeclInitVar(id, value, forceVar)

    // Augment ctx for the following instructions
    val funCtx2 = funCtx.extend(x)
    val rest    = convertToStmt(rest1)(funCtx2)

    stmt ~ rest
  }


  // Create a new variable for the given value, potentially immutable, and initialize it
  private def buildDeclInitVar(id: Identifier, v: Expr, forceVar: Boolean)
                              (implicit funCtx: FunCtx): (CAST.Var, CAST.Stmt) = {
    val valueF = convertAndFlatten(v)
    val typ    = v.getType

    valueF.value match {
      case CAST.IfElse(cond, thn, elze) =>
        val x      = buildVar(id, typ)
        val decl   = CAST.DeclVar(x)
        val ifelse = buildIfElse(cond, injectAssign(x, thn), injectAssign(x, elze))
        val init   = decl ~ ifelse

        (x, valueF.body ~~ init)

      case value =>
        val x    = if (forceVar) buildVar(id, typ) else buildVal(id, typ)
        val init = CAST.DeclInitVar(x, value)

        (x, valueF.body ~~ init)
    }
  }

  private def buildBinOp(lhs: Expr, op: String, rhs: Expr)(implicit funCtx: FunCtx) = {
    buildMultiOp(op, lhs :: rhs :: Nil)
  }

  private def buildUnOp(op: String, rhs1: Expr)(implicit funCtx: FunCtx) = {
    val rhsF = convertAndFlatten(rhs1)
    rhsF.body ~~ CAST.Op(op, rhsF.value)
  }

  private def buildMultiOp(op: String, exprs: Seq[Expr])(implicit funCtx: FunCtx): CAST.Stmt = {
    require(exprs.length >= 2)

    val stmts = exprs map convertToStmt
    val types = exprs map { e => convertToType(e.getType) }

    buildMultiOp(op, stmts, types)
  }

  private def buildMultiOp(op: String, stmts: Seq[CAST.Stmt], types: Seq[CAST.Type]): CAST.Stmt = {
      // Default operator constuction when either pure statements are involved
      // or no shortcut can happen
      def defaultBuild = {
        val fs = normaliseExecution(stmts, types)
        fs.bodies ~~ CAST.Op(op, fs.values)
      }

      if (stmts forall { _.isPureValue }) defaultBuild
      else op match {
      case "&&" =>
        // Apply short-circuit if needed
        if (stmts.length == 2) {
          // Base case:
          // { { a; v } && { b; w } }
          // is mapped onto
          // { a; if (v) { b; w } else { false } }
          val av = flatten(stmts(0))
          val bw = stmts(1)

          if (bw.isPureValue) defaultBuild
          else av.body ~~ buildIfElse(av.value, bw, CAST.False)
        } else {
          // Recursive case:
          // { { a; v } && ... }
          // is mapped onto
          // { a; if (v) { ... } else { false } }
          val av = flatten(stmts(0))
          val rest = buildMultiOp(op, stmts.tail, types.tail)

          if (rest.isPureValue) defaultBuild
          else av.body ~~ buildIfElse(av.value, rest, CAST.False)
        }

      case "||" =>
        // Apply short-circuit if needed
        if (stmts.length == 2) {
          // Base case:
          // { { a; v } || { b; w } }
          // is mapped onto
          // { a; if (v) { true } else { b; w } }
          val av = flatten(stmts(0))
          val bw = stmts(1)

          if (bw.isPureValue) defaultBuild
          else av.body ~~ buildIfElse(av.value, CAST.True, bw)
        } else {
          // Recusrive case:
          // { { a; v } || ... }
          // is mapped onto
          // { a; if (v) { true } else { ... } }
          val av = flatten(stmts(0))
          val rest = buildMultiOp(op, stmts.tail, types.tail)

          if (rest.isPureValue) defaultBuild
          else av.body ~~ buildIfElse(av.value, CAST.True, rest)
        }

      case _ =>
        defaultBuild
    }
  }

  // Flatten `if (if (cond1) thn1 else elze1) thn2 else elze2`
  // into `if (cond1) { if (thn1) thn2 else elz2 } else { if (elz1) thn2 else elze2 }`
  // or, if possible, into `if ((cond1 && thn1) || elz1) thn2 else elz2`
  //
  // Flatten `if (true) thn else elze` into `thn`
  // Flatten `if (false) thn else elze` into `elze`
  private def buildIfElse(cond: CAST.Stmt, thn2: CAST.Stmt, elze2: CAST.Stmt): CAST.Stmt = {
    val condF = flatten(cond)

    val ifelse = condF.value match {
      case CAST.IfElse(cond1, thn1, elze1) =>
        if (cond1.isPure && thn1.isPure && elze1.isPure) {
          val bools = CAST.Bool :: CAST.Bool :: Nil
          val ands  = cond1 :: thn1 :: Nil
          val ors   = buildMultiOp("&&", ands, bools) :: elze1 :: Nil
          val condX = buildMultiOp("||", ors, bools)
          CAST.IfElse(condX, thn2, elze2)
        } else {
          buildIfElse(cond1, buildIfElse(thn1, thn2, elze2), buildIfElse(elze1, thn2, elze2))
        }

      case CAST.True  => thn2
      case CAST.False => elze2
      case cond2      => CAST.IfElse(cond2, thn2, elze2)
    }

    condF.body ~~ ifelse
  }

  private def injectReturn(stmt: CAST.Stmt): CAST.Stmt = {
    val f = flatten(stmt)

    f.value match {
      case CAST.IfElse(cond, thn, elze) =>
        f.body ~~ CAST.IfElse(cond, injectReturn(thn), injectReturn(elze))

      case _ =>
        f.body ~~ CAST.Return(f.value)
    }
  }

  private def injectAssign(x: CAST.Var, stmt: CAST.Stmt): CAST.Stmt = {
    injectAssign(CAST.AccessVar(x.id), stmt)
  }

  private def injectAssign(x: CAST.Stmt, stmt: CAST.Stmt): CAST.Stmt = {
    val f = flatten(stmt)

    f.value match {
      case CAST.IfElse(cond, thn, elze) =>
        f.body ~~ CAST.IfElse(cond, injectAssign(x, thn), injectAssign(x, elze))

      case _ =>
        f.body ~~ CAST.Assign(x, f.value)
    }
  }

  // Flattened represents a non-empty statement { a; b; ...; y; z }
  // split into body { a; b; ...; y } and value z
  private case class Flattened(value: CAST.Stmt, body: Seq[CAST.Stmt])

  // FlattenedSeq does the same as Flattened for a sequence of non-empty statements
  private case class FlattenedSeq(values: Seq[CAST.Stmt], bodies: Seq[CAST.Stmt])

  private def flatten(stmt: CAST.Stmt) = stmt match {
    case CAST.Compound(stmts) if stmts.isEmpty => internalError(s"Empty compound cannot be flattened")
    case CAST.Compound(stmts)                  => Flattened(stmts.last, stmts.init)
    case stmt                                  => Flattened(stmt, Seq())
  }

  private def convertAndFlatten(expr: Expr)(implicit funCtx: FunCtx) = flatten(convertToStmt(expr))

  // Normalise execution order of, for example, function parameters;
  // `types` represents the expected type of the corresponding values
  // in case an intermediary variable needs to be created
  private def convertAndNormaliseExecution(exprs: Seq[Expr], types: Seq[CAST.Type])
                                          (implicit funCtx: FunCtx) = {
    require(exprs.length == types.length)
    normaliseExecution(exprs map convertToStmt, types)
  }

  private def normaliseExecution(typedStmts: Seq[(CAST.Stmt, CAST.Type)]): FlattenedSeq =
    normaliseExecution(typedStmts map { _._1 }, typedStmts map { _._2 })

  private def normaliseExecution(stmts: Seq[CAST.Stmt], types: Seq[CAST.Type]): FlattenedSeq = {
    require(stmts.length == types.length)

    // Create temporary variables if needed
    val stmtsFs = stmts map flatten
    val fs = (stmtsFs zip types) map {
      case (f, _) if f.value.isPureValue => f

      case (f, typ) =>
        // Similarly to buildDeclInitVar:
        val (tmp, body) = f.value match {
          case CAST.IfElse(cond, thn, elze) =>
            val tmp    = CAST.FreshVar(typ.mutable, "normexec")
            val decl   = CAST.DeclVar(tmp)
            val ifelse = buildIfElse(cond, injectAssign(tmp, thn), injectAssign(tmp, elze))
            val body   = f.body ~~ decl ~ ifelse

            (tmp, body)

          case value =>
            val tmp  = CAST.FreshVal(typ, "normexec")
            val body = f.body ~~ CAST.DeclInitVar(tmp, f.value)

            (tmp, body)
        }

        val value = CAST.AccessVar(tmp.id)
        flatten(body ~ value)
    }

    val empty  = Seq[CAST.Stmt]()
    val bodies = fs.foldLeft(empty){ _ ++ _.body }
    val values = fs map { _.value }

    FlattenedSeq(values, bodies)
  }

  private def containsArrayType(typ: TypeTree): Boolean = typ match {
    case Int32Type            => false
    case BooleanType          => false
    case UnitType             => false
    case ArrayType(_)         => true
    case TupleType(bases)     => bases exists containsArrayType
    case CaseClassType(cd, _) => cd.fields map { _.getType } exists containsArrayType
  }

  private def internalError(msg: String) = ctx.reporter.internalError(msg)
  private def fatalError(msg: String)    = ctx.reporter.fatalError(msg)
  private def debug(msg: String)         = ctx.reporter.debug(msg)(utils.DebugSectionGenC)

}

