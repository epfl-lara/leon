/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package phases

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.{ ExprOps, TypeOps, TreeTransformer }
import purescala.Types._
import xlang.Expressions._

import utils.Position

import ExtraOps._

import ir.{ PrimitiveTypes => PT, Literals => L, Operators => O }
import ir.IRs.{ CIR }

import scala.collection.mutable.{ Map => MutableMap }

/*
 * This phase takes a set of definitions (the Dependencies) and the fonction context database (FunCtxDB)
 * and produces an equivalent program expressed in the intermediate representation without generic types (CIR).
 *
 * NOTE This phase also rejects fragment of Scala that are not supported by GenC, such as returning
 *      or copying arrays, constructing a case class with mutable fields from function arguments,
 *      the >> operator, some forms of membership tests, the unapply pattern matching construct,
 *      and more.
 */
private[genc] object Scala2IRPhase extends TimedLeonPhase[(Dependencies, FunCtxDB), CIR.ProgDef] {
  val name = "Scala to IR converter"
  val description = "Convert the Scala AST into GenC's IR"

  def getTimer(ctx: LeonContext) = ctx.timers.genc.get("Scala -> CIR")

  def apply(ctx: LeonContext, input: (Dependencies, FunCtxDB)): CIR.ProgDef = {
    val reporter = MiniReporter(ctx)
    import reporter._

    val (deps, ctxDB) = input
    val entryPoint = getEntryPoint(deps.deps)

    val impl = new S2IRImpl(ctx, ctxDB, deps)
    val ir = CIR.ProgDef(impl(entryPoint))

    debugTree("RESULTING CIR", ir)

    ir
  }

  private def getEntryPoint(deps: Set[Definition]): FunDef = {
    val opt = deps collectFirst {
      case fd: FunDef if fd.id.name == "_main" => fd
    }

    opt.get // If not defined, the previous phase did something wrong.
  }

}


private class S2IRImpl(val ctx: LeonContext, val ctxDB: FunCtxDB, val deps: Dependencies) extends MiniReporter {

  /****************************************************************************************************
   *                                                       Entry point of conversion                  *
   ****************************************************************************************************/
  def apply(entryPoint: FunDef): CIR.FunDef = rec(entryPoint.typed)(Map.empty)



  /****************************************************************************************************
   *                                                       Caches                                     *
   ****************************************************************************************************/

  // For functions, we associate each TypedFunDef to a CIR.FunDef for each "type context" (TypeMapping).
  // This is very important for (non-generic) functions nested in a generic function because for N
  // instantiation of the outer function we have only one TypedFunDef for the inner function.
  private val funCache = MutableMap[(TypedFunDef, TypeMapping), CIR.FunDef]()

  private val classCache = MutableMap[ClassType, CIR.ClassDef]()



  /****************************************************************************************************
   *                                                       Helper functions                           *
   ****************************************************************************************************/
  // When converting expressions, we keep track of the variable in scope to build Bindings
  // Also, the identifier might not have the correct type (e.g. when generic). We therefore
  // need an external *concrete* type.
  private type Env = Map[(Identifier, TypeTree), CIR.ValDef]

  // Keep track of generic to concrete type mapping
  private type TypeMapping = Map[TypeParameter, TypeTree]

  private def instantiate(typ: TypeTree, tm: TypeMapping): TypeTree =
    TypeOps.instantiateType(typ, tm)

  // Here, when context are translated, there might remain some generic types. We use `tm` to make them disapear.
  private def convertVarInfoToArg(vi: VarInfo)(implicit tm: TypeMapping) = CIR.ValDef(rec(vi.id), rec(vi.typ), vi.isVar)
  private def convertVarInfoToParam(vi: VarInfo)(implicit tm: TypeMapping) = CIR.Binding(convertVarInfoToArg(vi))

  // Extract the ValDef from the known one
  private def buildBinding(id: Identifier)(implicit env: Env, tm: TypeMapping) = {
    val typ = instantiate(id.getType, tm)
    val optVd = env.get(id -> typ)
    val vd = optVd match {
      case Some(vd) => vd
      case None =>
        // Identifiers in Leon are known to be tricky when it comes to unique id.
        // It sometimes happen that the unique id are not in sync, especially with
        // generics. Here we try to find the best match based on the name only.
        warning(s"Working around issue with identifiers on $id...")
        env collectFirst {
          case ((eid, etype), evd) if eid.name == id.name && etype == typ => evd
        } getOrElse {
          internalError(s"Couldn't find a ValDef for $id in the environment: $env")
        }
    }
    CIR.Binding(vd)
  }

  private def buildLet(x: Identifier, e: Expr, body: Expr, isVar: Boolean)
                      (implicit env: Env, tm: TypeMapping): CIR.Expr = {
    val vd = CIR.ValDef(rec(x), rec(x.getType), isVar)
    val decl = CIR.DeclInit(vd, rec(e))
    val newEnv = env + ((x, instantiate(x.getType, tm)) -> vd)
    val rest = rec(body)(newEnv, tm)

    CIR.buildBlock(Seq(decl, rest))
  }

  // Include the "nesting path" in case of generic functions to avoid ambiguity
  private def buildId(tfd: TypedFunDef)(implicit tm: TypeMapping): CIR.Id =
    rec(tfd.fd.id) + (if (tfd.tps.nonEmpty) buildIdPostfix(tfd.tps) else buildIdFromTypeMapping(tm))

  private def buildId(ct: ClassType)(implicit tm: TypeMapping): CIR.Id =
    rec(ct.classDef.id) + buildIdPostfix(ct.tps)

  private def buildIdPostfix(tps: Seq[TypeTree])(implicit tm: TypeMapping): CIR.Id = if (tps.isEmpty) "" else {
    "_" + (tps filterNot { _ == Untyped } map rec map CIR.repId mkString "_")
  }

  private def buildIdFromTypeMapping(tm: TypeMapping): CIR.Id = if (tm.isEmpty) "" else {
    "_" + (tm.values map { t => CIR.repId(rec(t)(tm)) } mkString "_")
  }

  // Check validity of the operator
  //
  // NOTE the creation of equals functions for `==` is deferred to a later phase.
  private def checkOp(op: O.Operator, ops: Seq[CIR.Type], pos: Position): Unit = {
    assert(ops.nonEmpty)

    def check(b: Boolean) = if (!b) {
      fatalError(s"Invalid use of operator $op with the given operands", pos)
    }

    def isLogical: Boolean = ops forall { _.isLogical }
    def isIntegral: Boolean = ops forall { _.isIntegral }
    def isPairOfT: Boolean = (ops.size == 2) && (ops forall { _ == ops(0) }) // or use <=???

    op match {
      case _: O.FromPairOfT => check(isPairOfT)
      case _: O.FromLogical => check(isLogical)
      case _: O.FromIntegral => check(isIntegral)
      case _ => internalError(s"Unhandled check of operator $op")
    }
  }

  // Prevent some form of aliasing that verification supports but our memory model doesn't.
  // See Chapter 4: Memory, Aliasing & Mutability Models For GenC
  //     of Extending Safe C Support In Leon.
  private def checkConstructArgs(args: Seq[(CIR.Expr, Position)]): Unit = {
    // Reject arguments that have mutable type (but allow var, and arrays)
    def isRefToMutableVar(arg: (CIR.Expr, Position)): Boolean = arg._1 match {
      case CIR.Binding(vd) => vd.getType.isMutable && !vd.getType.isArray
      case _ => false
    }

    args find isRefToMutableVar match {
      case Some((_, pos)) =>
        fatalError(s"Invalid reference: cannot construct an object from a mutable variable.", pos)

      case _ =>
    }
  }

  private def buildBinOp(lhs0: Expr, op: O.BinaryOperator, rhs0: Expr)
                        (pos: Position)
                        (implicit env: Env, tm: TypeMapping) = {
    val lhs = rec(lhs0)
    val rhs = rec(rhs0)

    checkOp(op, Seq(lhs.getType, lhs.getType), pos)

    CIR.BinOp(op, lhs, rhs)
  }

  private def buildUnOp(op: O.UnaryOperator, expr0: Expr)
                       (pos: Position)
                       (implicit env: Env, tm: TypeMapping) = {
    val expr = rec(expr0)

    checkOp(op, Seq(expr.getType), pos)

    CIR.UnOp(op, expr)
  }

  // Create a binary AST
  private def buildMultiOp(op: O.BinaryOperator, exprs: Seq[Expr])
                          (pos: Position)
                          (implicit env: Env, tm: TypeMapping): CIR.BinOp = exprs.toList match {
    case Nil => internalError("no operands")
    case a :: Nil => internalError("at least two operands required")
    case a :: b :: Nil => buildBinOp(a, op, b)(pos)
    case a :: xs => CIR.BinOp(op, rec(a), buildMultiOp(op, xs)(pos))
  }

  // Tuples are converted to classes
  private def tuple2Class(typ: TypeTree)(implicit tm: TypeMapping): CIR.ClassDef = typ match {
    case TupleType(bases) =>
      val types = bases map rec
      val fields = types.zipWithIndex map { case (typ, i) => CIR.ValDef("_" + (i+1), typ, isVar = false) }
      val id = "Tuple" + buildIdPostfix(bases)
      CIR.ClassDef(id, None, fields, isAbstract = false)

    case _ => internalError("Unexpected ${typ.getClass} instead of TupleType")
  }

  private def buildCast(e0: Expr, newType0: BitVectorType)(implicit env: Env, tm: TypeMapping): CIR.IntegralCast = {
    val newType = newType0.size match {
      case 8 => PT.Int8Type
      case 32 => PT.Int32Type
      case s => internalError("Unsupported integral cast to $s-bit integer")
    }

    val e = rec(e0)

    CIR.IntegralCast(e, newType)
  }

  private def castNotSupported(ct: ClassType): Boolean =
    ct.classDef.isAbstract && ct.classDef.hasParent

  // Freshen the identifiers of new variable definitions and keeps free variables as is.
  private def freshen(e: Expr): Expr = {
    val freshIds = MutableMap[Identifier, Identifier]()

    val transformer = new TreeTransformer {
      override def transform(id: Identifier) = freshIds.getOrElse(id, id)

      override def transform(e: Expr)(implicit bindings: Map[Identifier, Identifier]): Expr = e match {
        case Let(x, v, b) =>
          val y = x.freshen
          freshIds += x -> y
          super.transform(Let(y, v, b))

        case LetVar(x, v, b) =>
          val y = x.freshen
          freshIds += x -> y
          super.transform(LetVar(y, v, b))

        case e => super.transform(e)
      }
    }

    transformer.transform(e)(Map.empty)
  }



  /****************************************************************************************************
   *                                                       Pattern Matching helper functions          *
   ****************************************************************************************************/
  // NOTE We don't rely on ExprOps.matchToIfThenElse because it doesn't apply well with
  //      side-effects and type casting.

  private case class PMCase(cond: CIR.Expr, guardOpt: Option[CIR.Expr], body: CIR.Expr) {
    def fullCondition: CIR.Expr = guardOpt match {
      case None => cond
      case Some(guard) if cond == CIR.True => guard
      case Some(guard) => CIR.BinOp(O.And, cond, guard)
    }
  }

  private object ElseCase {
    def unapply(caze: PMCase): Option[CIR.Expr] = {
      if (CIR.True == caze.fullCondition) Some(caze.body)
      else None
    }
  }

  private def convertPatMap(scrutinee0: Expr, cases0: Seq[MatchCase])(implicit env: Env, tm: TypeMapping): CIR.Expr = {
    require(cases0.nonEmpty)

    def withTmp(typ: TypeTree, value: Expr, env: Env): (Variable, Some[CIR.DeclInit], Env) = {
      val tmp0 = FreshIdentifier("tmp", typ)
      val tmpId = rec(tmp0)
      val tmpTyp = rec(typ)
      val tmp = CIR.ValDef(tmpId, tmpTyp, isVar = false)
      val pre = CIR.DeclInit(tmp, rec(value)(env, tm))

      (tmp0.toVariable, Some(pre), env + ((tmp0, instantiate(typ, tm)) -> tmp))
    }

    def scrutRec(scrutinee0: Expr): (Expr, Option[CIR.Expr], Env) = scrutinee0 match {
      case v: Variable => (v, None, env)

      case Block(Nil, v: Variable) => (v, None, env)
      case Block(init, v: Variable) => (v, Some(rec(Block(init.init, init.last))), env)

      case field @ CaseClassSelector(_, _: Variable, _) => (field, None, env)

      case select @ ArraySelect(_: Variable, _: Variable | _: IntLiteral) => (select, None, env)
      case select @ ArraySelect(array: Variable, index) =>
        // Save idx into a temporary variable, but apply patmat on array access.
        // This way, the index is computed once only.
        val (newIndex, preOpt, newEnv) = withTmp(Int32Type, index, env)
        val newSelect = ArraySelect(array, newIndex)
        (newSelect, preOpt, newEnv)

      case select @ ArraySelect(a, i) =>
        internalError(s"array select $a[$i] is not supported; ${a.getClass} - ${i.getClass}")

      case Assert(_, _, body) => scrutRec(body)

      case _: FunctionInvocation | _: CaseClass | _: LetVar | _: Let | _: Tuple | _: IfExpr =>
        withTmp(scrutinee0.getType, scrutinee0, env)

      case e => internalError(s"scrutinee = $e of type ${e.getClass} is not supported")
    }

    val (scrutinee, preOpt, newEnv) = scrutRec(scrutinee0)

    val cases = cases0 map { caze => convertCase(scrutinee, caze)(newEnv, tm) }

    // Identify the last case
    val last = cases.last match {
      case ElseCase(body) => body
      case caze => CIR.If(caze.fullCondition, caze.body)
    }

    // Combine all cases, using a foldRight
    val patmat = (cases.init :\ last) { case (caze, acc) =>
      CIR.IfElse(caze.fullCondition, caze.body, acc)
    }

    preOpt match {
      case None => patmat
      case Some(pre) => CIR.buildBlock(pre :: patmat :: Nil)
    }
  }

  // Substitute a binder (id) by the scrutinee (or a more appropriate expression) in the given expression
  private def substituteBinder(id: Identifier, replacement: Expr, expr: Expr): Expr =
    ExprOps.replaceFromIDs(Map(id -> replacement), expr)

  private def buildConjunction(exprs: Seq[CIR.Expr]): CIR.Expr = exprs.foldRight[CIR.Expr](CIR.True) { case (e, acc) =>
    if (e == CIR.True) acc // Don't add trivialities in the conjunction
    else if (acc == CIR.True) e
    else CIR.BinOp(O.And, e, acc)
  }

  // Extract the condition, guard and body (rhs) of a match case
  private def convertCase(initialScrutinee: Expr, caze: MatchCase)(implicit env: Env, tm: TypeMapping): PMCase = {
    // We need to keep track of binder (and binders in sub-patterns) and their appropriate
    // substitution. We do so in an Imperative manner with variables -- sorry FP, but it's
    // much simpler that way! However, to encapsulate things a bit, we use the `update`
    // function to update both the guard and rhs safely. When we have finished converting
    // every cases, we'll be able to convert the guard and rhs to IR.
    var guardOpt = caze.optGuard
    var body = caze.rhs

    def update(binderOpt: Option[Identifier], replacement: Expr): Unit = binderOpt match {
      case Some(binder) =>
        guardOpt = guardOpt map { guard => substituteBinder(binder, replacement, guard) }
        body = substituteBinder(binder, replacement, body)

      case None => ()
    }

    // For the main pattern and its subpatterns, we keep track of the "current" scrutinee
    // expression (after cast, field access, and other similar operations).
    def ccRec(pat: Pattern, scrutinee: Expr): CIR.Expr = pat match {
      case InstanceOfPattern(b, ct) =>
        val cast = AsInstanceOf(scrutinee, ct)
        update(b, cast)

        rec(IsInstanceOf(scrutinee, ct))

      case WildcardPattern(b) =>
        update(b, scrutinee)
        CIR.True

      case CaseClassPattern(b, ct, subs) =>
        val (checkType, cast) =
          if (scrutinee.getType == ct) CIR.True -> scrutinee // Omit useless type checks & casts
          else rec(IsInstanceOf(scrutinee, ct)) -> AsInstanceOf(scrutinee, ct)

        update(b, cast)

        // Use the classDef fields to have the original identifiers!
        val checkSubs = (ct.classDef.fields zip subs) map { case (field, sub) =>
          ccRec(sub, CaseClassSelector(ct, cast, field.id))
        }

        // Luckily, there are no block involved so we can have a simple conjunction
        buildConjunction(checkType +: checkSubs)

      case TuplePattern(b, subs) =>
        // Somewhat similar to CaseClassPattern, but simpler
        update(b, scrutinee)

        val checkSubs = subs.zipWithIndex map { case (sub, index) =>
          ccRec(sub, TupleSelect(scrutinee, index+1))
        }

        buildConjunction(checkSubs)

      case LiteralPattern(b, lit) =>
        update(b, scrutinee)
        buildBinOp(scrutinee, O.Equals, lit)(pat.getPos)

      case UnapplyPattern(bind, unapply, subs) =>
        fatalError(s"Unapply Pattern, a.k.a. Extractor Objects, is not supported", pat.getPos)
    }

    val cond = ccRec(caze.pattern, initialScrutinee)

    PMCase(cond, guardOpt map rec, rec(body))
  }



  /****************************************************************************************************
   *                                                       Recursive conversion                       *
   ****************************************************************************************************/
  private def rec(id: Identifier): CIR.Id = {
    if (id.name == "_main") "_main"
    else id.uniqueNameDelimited("_")
  }

  // Try first to fetch the function from cache to handle recursive funcitons.
  private def rec(tfd: TypedFunDef)(implicit tm0: TypeMapping): CIR.FunDef = funCache get tfd -> tm0 getOrElse {
    val id = buildId(tfd)

    // Warn user about recusrivity: this is not MISRA complient unless it is very tightly controlled.
    // NOTE this check is done after VC are removed.
    if (tfd.fd.isRecursive(deps.prog))
      warning(s"MISRA rules state that recursive functions should be very tightly controlled; ${tfd.id} is recursive")

    // We have to manually specify tm1 from now on to avoid using tm0. We mark tm1 as
    // implicit as well to generate ambiguity at compile time to avoid forgetting a call site.
    implicit val tm1 = tm0 ++ tfd.typesMap

    // Make sure to get the id from the function definition, not the typed one, as they don't always match.
    val paramTypes = tfd.fd.params map { p => rec(p.getType)(tm1) }
    val paramIds = tfd.fd.params map { p => rec(p.id) }
    val params = (paramIds zip paramTypes) map { case (id, typ) => CIR.ValDef(id, typ, isVar = false) }

    // Extract the context for the function definition, taking care of the remaining generic types in the context.
    val ctx = ctxDB(tfd.fd) map { c => convertVarInfoToArg(c)(tm1) }

    val returnType = rec(tfd.returnType)(tm1)
    if (returnType.containsArray)
      fatalError("Returning arrays from function is not supported", tfd.getPos)

    // Build a partial function without body in order to support recursive functions
    val fun = CIR.FunDef(id, returnType, ctx, params, null)
    funCache.update(tfd -> tm0, fun) // Register with the callee TypeMapping, *not* the newer

    // Now proceed with the body
    val body: CIR.FunBody =
      if (tfd.fd.isManuallyDefined) {
        val impl = tfd.fd.getManualDefinition
        CIR.FunBodyManual(impl.includes, impl.code)
      } else {
        // Build the new environment from context and parameters
        val ctxKeys = ctxDB(tfd.fd) map { c => c.id -> instantiate(c.typ, tm1) }
        val ctxEnv = ctxKeys zip ctx

        val paramKeys = tfd.fd.params map { p => p.id -> instantiate(p.getType, tm1) }
        val paramEnv = paramKeys zip params

        val env = (ctxEnv ++ paramEnv).toMap

        // Recurse on the FunDef body, and not the TypedFunDef one, in order to keep the correct identifiers.
        CIR.FunBodyAST(rec(tfd.fd.fullBody)(env, tm1))
      }

    // Now that we have a body, we can fully build the FunDef
    fun.body = body

    fun
  }

  // We need a type mapping only when converting context argument to remove the remaining generics.
  private def rec(typ: TypeTree)(implicit tm: TypeMapping): CIR.Type = typ match {
    case UnitType => CIR.PrimitiveType(PT.UnitType)
    case BooleanType => CIR.PrimitiveType(PT.BoolType)
    case Int8Type => CIR.PrimitiveType(PT.Int8Type)
    case Int32Type => CIR.PrimitiveType(PT.Int32Type)
    case CharType => CIR.PrimitiveType(PT.CharType)
    case StringType => CIR.PrimitiveType(PT.StringType)

    // For both case classes and abstract classes:
    case ct: ClassType =>
      val cd = ct.classDef
      if (cd.isDropped) {
        CIR.DroppedType
      } else if (cd.isManuallyTyped) {
        val typedef = cd.getManualType
        CIR.TypedefType(cd.id.name, typedef.alias, typedef.include)
      } else {
        CIR.ClassType(rec(ct))
      }

    case ArrayType(base) => CIR.ArrayType(rec(base))

    case TupleType(_) => CIR.ClassType(tuple2Class(typ))

    case FunctionType(from, to) => CIR.FunType(ctx = Nil, params = from map rec, ret = rec(to))

    case tp: TypeParameter => rec(instantiate(tp, tm))

    case t => internalError(s"type tree of type ${t.getClass} not handled")
  }

  private def rec(ct: ClassType)(implicit tm: TypeMapping): CIR.ClassDef = {
    // Convert the whole class hierarchy to register all siblings, in a top down fasion, that way
    // each children class in the the CIR hierarchy get registered to its parent and we can keep track
    // of all of them.

    type Translation = Map[ClassType, CIR.ClassDef]

    def recTopDown(ct: ClassType, parent: Option[CIR.ClassDef], acc: Translation): Translation = {
      if (ct.classDef.isDropped || ct.classDef.isManuallyTyped)
        internalError(s"${ct.id} is not convertible to ClassDef!")

      val id = buildId(ct)
      assert(!ct.classDef.isCaseObject)

      // Use the class definition id, not the typed one as they might not match.
      val fieldTypes = ct.fieldsTypes map rec
      val fields = (ct.classDef.fields zip fieldTypes) map { case (vd, typ) => CIR.ValDef(rec(vd.id), typ, vd.isVar) }

      val clazz = CIR.ClassDef(id, parent, fields, ct.classDef.isAbstract)

      val newAcc = acc + (ct -> clazz)

      // Recurse down
      val children = ct.classDef.knownChildren map { _.typed(ct.tps) }
      (newAcc /: children) { case (currentAcc, child) => recTopDown(child, Some(clazz), currentAcc) }
    }

    val translation = recTopDown(ct.root, None, Map.empty)

    translation(ct)
  }

  private def rec(e: Expr)(implicit env: Env, tm0: TypeMapping): CIR.Expr = e match {
    /* Ignore static assertions */
    case Require(_, body) => rec(body)
    case Ensuring(body, _) => rec(body)
    case Assert(_, _, body) => rec(body)

    case UnitLiteral() => CIR.Lit(L.UnitLit)
    case BooleanLiteral(v) => CIR.Lit(L.BoolLit(v))
    case ByteLiteral(v) => CIR.Lit(L.Int8Lit(v))
    case IntLiteral(v) => CIR.Lit(L.Int32Lit(v))
    case CharLiteral(v) => CIR.Lit(L.CharLit(v))
    case StringLiteral(v) => CIR.Lit(L.StringLit(v))

    case Block(es, last) => CIR.buildBlock((es :+ last) map rec)

    case Variable(id) => buildBinding(id)

    case Let(x, e, body) => buildLet(x, e, body, isVar = false)
    case LetVar(x, e, body) => buildLet(x, e, body, isVar = true)

    case Assignment(id, expr) => CIR.Assign(buildBinding(id), rec(expr))

    case FieldAssignment(obj, fieldId0, expr) =>
      // The fieldId might actually not be the correct one;
      // it's global counter might differ from the one in the class definition.
      val fieldId = obj.getType match {
        case ct: ClassType =>
          val fields = ct.classDef.fields
          val optFieldId = fields collectFirst { case field if field.id.name == fieldId0.name => field.id }
          optFieldId getOrElse { internalError(s"No corresponding field for $fieldId0 in class $ct") }

        case typ => internalError(s"Unexpected type $typ. Only class type are expected to update fields")
      }
      CIR.Assign(CIR.FieldAccess(rec(obj), rec(fieldId)), rec(expr))

    case LetDef(_, body) =>
      // We don't have to traverse the nested function now because we already have their respective context.
      rec(body)

    case FunctionInvocation(tfd, args0) =>
      val fun = rec(tfd)
      implicit val tm1 = tm0 ++ tfd.typesMap
      val extra = ctxDB(tfd.fd) map { c => convertVarInfoToParam(c)(tm1) }
      val args = args0 map { a0 => rec(a0)(env, tm1) }

      CIR.App(fun.toVal, extra, args)

    case Application(fun0, args0) =>
      // Contrary to FunctionInvocation, Application of function-like object do not have to extend their
      // context as no environment variables are allowed to be captured.
      val fun = rec(fun0) match {
        case e if e.getType.isInstanceOf[CIR.FunType] => CIR.FunRef(e)
        case e => fatalError(s"Expected a binding but got $e of type ${e.getClass}.", fun0.getPos)
      }
      val args = args0 map rec

      CIR.App(fun, Nil, args)

    case Lambda(argsA, FunctionInvocation(tfd, argsB))  =>
      // Lambda are okay for GenC iff they do not capture variables and call a function directly.
      // Additionally, the called function should not capture any environment variable.
      if ((argsA map { _.toVariable }) != argsB) {
        val strA = argsA.mkString("[", ", ", "]")
        val strB = argsB.mkString("[", ", ", "]")
        debug(s"This is a capturing lambda because: $strA != $strB")
        fatalError(s"Capturing lambda are not supported", e.getPos)
      }

      val fun = rec(tfd)

      if (fun.ctx.nonEmpty) {
        debug(s"${fun.id} is capturing some variables: ${fun.ctx mkString ", "}")
        fatalError(s"Function capturing their environment cannot be used as value", e.getPos)
      }

      fun.toVal

    case Lambda(args0, body0) =>
      debug(s"This is an unamed function; support is currently missing")
      debug(s"args = $args0, body = $body0 (${body0.getClass})")
      fatalError(s"Lambda are not (yet) supported", e.getPos)

    case CaseClass(cct, args0) =>
      val clazz = rec(cct)
      val args = args0 map rec
      val poss = args0 map { _.getPos }

      checkConstructArgs(args zip poss)

      CIR.Construct(clazz, args)

    case CaseClassSelector(_, obj, fieldId) => CIR.FieldAccess(rec(obj), rec(fieldId))

    case tuple @ Tuple(args0) =>
      val clazz = tuple2Class(tuple.getType)
      val args = args0 map rec
      val poss = args0 map { _.getPos }

      checkConstructArgs(args zip poss)

      CIR.Construct(clazz, args)

    case TupleSelect(tuple, idx) =>
      CIR.FieldAccess(rec(tuple), "_" + idx)

    case ArrayLength(array) => CIR.ArrayLength(rec(array))

    case ArraySelect(array, index) => CIR.ArrayAccess(rec(array), rec(index))

    case ArrayUpdated(array, index, newValue) => fatalError(s"Unsupported copy of array", e.getPos)

    case ArrayUpdate(array, index, value) =>
      CIR.Assign(CIR.ArrayAccess(rec(array), rec(index)), rec(value))

    case array @ NonemptyArray(empty, Some((value0, length0))) if empty.isEmpty =>
      val arrayType = rec(array.getType).asInstanceOf[CIR.ArrayType]

      // Convert to VLA or normal array
      val alloc = rec(length0) match {
        case CIR.Lit(L.Int32Lit(length)) =>
          // Optimisation for zero: don't generate values at all to speed up processing within GenC.
          val values = value0 match {
            case IntLiteral(0) | ByteLiteral(0) => Left(CIR.Zero)
            case value0 => Right((0 until length) map { _ => rec(freshen(value0)) }) // the same expression, != same runtime value
          }
          CIR.ArrayAllocStatic(arrayType, length, values)

        case length =>
          if (arrayType.base.containsArray)
            fatalError(s"VLAs cannot have elements being/containing other array", array.getPos)

          warning(s"VLAs should be avoid according to MISRA C rules", array.getPos)

          val value = rec(value0)
          CIR.ArrayAllocVLA(arrayType, length, value)
      }

      CIR.ArrayInit(alloc)

    case NonemptyArray(_, Some(_)) =>
      internalError("Inconsistent state of NonemptyArray")

    case array @ NonemptyArray(elems, None) => // Here elems is non-empty
      val arrayType = rec(array.getType).asInstanceOf[CIR.ArrayType]

      // Sort values according the the key (aka index)
      val indexes = elems.keySet.toSeq.sorted
      val values = indexes map { i => rec(elems(i)) }

      // Assert all types are the same
      if (values exists { _.getType != arrayType.base })
        fatalError("Heterogenous arrays", array.getPos)

      val alloc = CIR.ArrayAllocStatic(arrayType, values.length, Right(values))
      CIR.ArrayInit(alloc)

    case IfExpr(cond, thenn, NoTree(_)) => CIR.If(rec(cond), rec(thenn))
    case IfExpr(cond, thenn, elze) => CIR.IfElse(rec(cond), rec(thenn), rec(elze))

    case While(cond, body) => CIR.While(rec(cond), rec(body))

    case LessThan(lhs, rhs)       => buildBinOp(lhs, O.LessThan, rhs)(e.getPos)
    case GreaterThan(lhs, rhs)    => buildBinOp(lhs, O.GreaterThan, rhs)(e.getPos)
    case LessEquals(lhs, rhs)     => buildBinOp(lhs, O.LessEquals, rhs)(e.getPos)
    case GreaterEquals(lhs, rhs)  => buildBinOp(lhs, O.GreaterEquals, rhs)(e.getPos)
    case Equals(lhs, rhs)         => buildBinOp(lhs, O.Equals, rhs)(e.getPos)
    case Not(Equals(lhs, rhs))    => buildBinOp(lhs, O.NotEquals, rhs)(e.getPos)

    case Not(rhs)                 => buildUnOp(O.Not, rhs)(e.getPos)
    case And(exprs)               => buildMultiOp(O.And, exprs)(e.getPos)
    case Or(exprs)                => buildMultiOp(O.Or, exprs)(e.getPos)

    case BVPlus(lhs, rhs)         => buildBinOp(lhs, O.Plus, rhs)(e.getPos)
    case BVMinus(lhs, rhs)        => buildBinOp(lhs, O.Minus, rhs)(e.getPos)
    case BVUMinus(rhs)            => buildUnOp(O.UMinus, rhs)(e.getPos)
    case BVTimes(lhs, rhs)        => buildBinOp(lhs, O.Times, rhs)(e.getPos)
    case BVDivision(lhs, rhs)     => buildBinOp(lhs, O.Div, rhs)(e.getPos)
    case BVRemainder(lhs, rhs)    => buildBinOp(lhs, O.Modulo, rhs)(e.getPos)
    case BVNot(rhs)               => buildUnOp(O.BNot, rhs)(e.getPos)
    case BVAnd(lhs, rhs)          => buildBinOp(lhs, O.BAnd, rhs)(e.getPos)
    case BVOr(lhs, rhs)           => buildBinOp(lhs, O.BOr, rhs)(e.getPos)
    case BVXOr(lhs, rhs)          => buildBinOp(lhs, O.BXor, rhs)(e.getPos)
    case BVShiftLeft(lhs, rhs)    => buildBinOp(lhs, O.BLeftShift, rhs)(e.getPos)
    case BVAShiftRight(lhs, rhs)  => fatalError("Operator >> is not supported", e.getPos)
    case BVLShiftRight(lhs, rhs)  => buildBinOp(lhs, O.BRightShift, rhs)(e.getPos)

    case BVWideningCast(e, t)  => buildCast(e, t)
    case BVNarrowingCast(e, t) => buildCast(e, t)

    case MatchExpr(scrutinee, cases) => convertPatMap(scrutinee, cases)

    case IsInstanceOf(expr, ct) if castNotSupported(ct) =>
      fatalError(s"Membership tests on abstract classes are not supported", e.getPos)

    case IsInstanceOf(expr, ct) => CIR.IsA(rec(expr), CIR.ClassType(rec(ct)))

    case AsInstanceOf(expr, ct) if castNotSupported(ct) =>
      fatalError(s"Cast to abstract classes are not supported", e.getPos)

    case AsInstanceOf(expr, ct) => CIR.AsA(rec(expr), CIR.ClassType(rec(ct)))

    case e =>
      warning(s"Unhandled expression", e.getPos)
      internalError(s"expression `$e` of type ${e.getClass} not handled")
  }

}

