/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package phases

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.{ ExprOps }
import purescala.Types._
import xlang.Expressions._

import ExtraOps._

import ir.{ PrimitiveTypes => PT, Literals => L, Operators => O }
import ir.IRs.{ CIR }

import scala.collection.mutable.{ Map => MutableMap }

/*
 * This phase takes a set of definitions (the Dependencies) and the fonction context database (FunCtxDB)
 * and produces an equivalent program expressed in the intermediate representation without generic types (CIR).
 */
private[genc] object Scala2IRPhase extends TimedLeonPhase[(Dependencies, FunCtxDB), CIR.ProgDef] {
  val name = "Scala to IR converter"
  val description = "Convert the Scala AST into GenC's 'generic' IR"

  def getTimer(ctx: LeonContext) = ctx.timers.genc.get("Scala -> CIR")

  def apply(ctx: LeonContext, input: (Dependencies, FunCtxDB)): CIR.ProgDef = {
    val reporter = MiniReporter(ctx)
    import reporter._

    val (deps, ctxDB) = input
    val entryPoint = getEntryPoint(deps)

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
  def apply(entryPoint: FunDef): CIR.FunDef = rec(entryPoint.typed)



  /****************************************************************************************************
   *                                                       Caches                                     *
   ****************************************************************************************************/
  private val funCache = MutableMap[TypedFunDef, CIR.FunDef]()
  private val classCache = MutableMap[ClassType, CIR.ClassDef]()



  /****************************************************************************************************
   *                                                       Helper functions                           *
   ****************************************************************************************************/
  private def convertVarInfoToArg(vi: VarInfo) = CIR.ValDef(rec(vi.id), rec(vi.typ), vi.isVar)
  private def convertVarInfoToParam(vi: VarInfo) = CIR.Binding(convertVarInfoToArg(vi))

  // Extract the ValDef from the known one
  private def buildBinding(id: Identifier)(implicit env: Env) = CIR.Binding(env(id))

  private def buildLet(x: Identifier, e: Expr, body: Expr, isVar: Boolean)(implicit env: Env): CIR.Expr = {
    val vd = CIR.ValDef(rec(x), rec(x.getType), isVar)
    val decl = CIR.DeclInit(vd, rec(e))
    val newEnv = env + (x -> vd)
    val rest = rec(body)(newEnv)

    CIR.buildBlock(Seq(decl, rest))
  }

  private def buildId(tfd: TypedFunDef): CIR.Id =
    rec(tfd.fd.id) + buildIdPostfix(tfd.tps)

  private def buildId(ct: ClassType): CIR.Id =
    rec(ct.classDef.id) + buildIdPostfix(ct.tps)

  private def buildIdPostfix(tps: Seq[TypeTree]): CIR.Id = if (tps.isEmpty) "" else {
    "_" + (tps filterNot { _ == Untyped } map rec map CIR.repId mkString "_")
  }

  private def buildBinOp(lhs: Expr, op: O.BinaryOperator, rhs: Expr)(implicit env: Env) =
    CIR.BinOp(op, rec(lhs), rec(rhs))

  private def buildUnOp(op: O.UnaryOperator, expr: Expr)(implicit env: Env) =
    CIR.UnOp(op, rec(expr))

  // Create a binary AST
  private def buildMultiOp(op: O.BinaryOperator, exprs: Seq[Expr])(implicit env: Env): CIR.BinOp = exprs.toList match {
    case Nil => internalError("no operands")
    case a :: Nil => internalError("at least two operands required")
    case a :: b :: Nil => CIR.BinOp(op, rec(a), rec(b))
    case a :: xs => CIR.BinOp(op, rec(a), buildMultiOp(op, xs))
  }

  // Tuples are converted to classes
  private def tuple2Class(typ: TypeTree): CIR.ClassDef = typ match {
    case TupleType(bases) =>
      val types = bases map rec
      val fields = types.zipWithIndex map { case (typ, i) => CIR.ValDef("_" + (i+1), typ, isVar = false) }
      val id = "Tuple" + buildIdPostfix(bases)
      CIR.ClassDef(id, None, fields, isAbstract = false)

    case _ => internalError("Unexpected ${typ.getClass} instead of TupleType")
  }

  // When converting expressions, we keep track of the variable in scope to build Bindings
  type Env = Map[Identifier, CIR.ValDef]



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

  private def convertPatMap(scrutinee0: Expr, cases0: Seq[MatchCase])(implicit env: Env): CIR.Expr = {
    require(cases0.nonEmpty)

    def withTmp(typ: TypeTree, value: Expr, env: Env): (Variable, Some[CIR.DeclInit], Env) = {
      val tmp0 = FreshIdentifier("tmp", typ)
      val tmpId = rec(tmp0)
      val tmpTyp = rec(typ)
      val tmp = CIR.ValDef(tmpId, tmpTyp, isVar = false)
      val pre = CIR.DeclInit(tmp, rec(value)(env))

      (tmp0.toVariable, Some(pre), env + (tmp0 -> tmp))
    }

    val (scrutinee, preOpt, newEnv) = scrutinee0 match {
      case v: Variable => (v, None, env)
      case Block(Nil, v: Variable) => (v, None, env)
      case Block(init, v: Variable) => (v, Some(rec(Block(init.init, init.last))), env)

      case fi @ FunctionInvocation(_, _) => withTmp(scrutinee0.getType, fi, env)
      case cc @ CaseClass(_, _) => withTmp(scrutinee0.getType, cc, env)

      case e => internalError(s"scrutinee = $e of type ${e.getClass} is not supported")
    }

    val cases = cases0 map { caze => convertCase(scrutinee, caze)(newEnv) }

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
  private def convertCase(initialScrutinee: Expr, caze: MatchCase)(implicit env: Env): PMCase = {
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
        val cast = AsInstanceOf(scrutinee, ct)
        update(b, cast)

        val checkType = rec(IsInstanceOf(scrutinee, ct))
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
        buildBinOp(scrutinee, O.Equals, lit)

      case UnapplyPattern(bind, unapply, subs) =>
        fatalError(s"Unapply Pattern, a.k.a. Extractor Objects", pat.getPos)
    }

    val cond = ccRec(caze.pattern, initialScrutinee)

    PMCase(cond, guardOpt map rec, rec(body))
  }



  /****************************************************************************************************
   *                                                       Recursive conversion                       *
   ****************************************************************************************************/
  private def rec(id: Identifier): CIR.Id = {
    if (id.name == "_main") "_main"
    else {
      val uniqueId = id.uniqueNameDelimited("_")
      if (uniqueId endsWith "_1") id.name // when possible, keep the id as clean as possible
      else uniqueId
    }

  }

  // Try first to fetch the function from cache to handle recursive funcitons.
  private def rec(tfd: TypedFunDef): CIR.FunDef = funCache get tfd getOrElse {
    val id = buildId(tfd)

    // Make sure to get the id from the function definition, not the typed one, as they don't always match.
    val paramTypes = tfd.params map { p => rec(p.getType) }
    val paramIds = tfd/*.fd*/.params map { p => rec(p.id) }
    val params = (paramIds zip paramTypes) map { case (id, typ) => CIR.ValDef(id, typ, isVar = false) }

    // Extract the context for the function definition.
    val ctx = ctxDB(tfd.fd) map convertVarInfoToArg
    // TODO THERE MIGHT BE SOME GENERICS IN THE CONTEXT!!!

    val returnType = rec(tfd.returnType)

    // Build a partial function without body in order to support recursive functions
    val fun = CIR.FunDef(id, returnType, ctx, params, null)
    funCache.update(tfd, fun)

    // Now proceed with the body
    val body: CIR.FunBody =
      if (tfd.fd.isManuallyDefined) {
        val impl = tfd.fd.getManualDefinition
        CIR.FunBodyManual(impl.includes, impl.code)
      } else {
        val ctxEnv = (ctxDB(tfd.fd) map { _.id }) zip ctx
        val paramEnv = (tfd/*.fd*/.params map { _.id }) zip params
        val env = (ctxEnv ++ paramEnv).toMap

        // TODO Find out if this is an issue or not by writing a regression test.
        warning(s"we are invalidating the ctx names because we are using the translated version of the body of $id")

        CIR.FunBodyAST(rec(tfd.fullBody)(env))
      }

    // Now that we have a body, we can fully build the FunDef
    fun.body = body

    fun
  }

  private def rec(typ: TypeTree): CIR.Type = typ match {
    case UnitType => CIR.PrimitiveType(PT.UnitType)
    case BooleanType => CIR.PrimitiveType(PT.BoolType)
    case Int32Type => CIR.PrimitiveType(PT.Int32Type)
    case CharType => CIR.PrimitiveType(PT.CharType)
    case StringType => CIR.PrimitiveType(PT.StringType)

    // case tp @ TypeParameter(_) => CIR.ParametricType(convertId(tp.id))

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

    case FunctionType(from, to) => internalError(s"what shoud I do with $from -> $to")

    case t => internalError(s"type tree of type ${t.getClass} not handled")
  }

  private def rec(ct: ClassType): CIR.ClassDef = {
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

  private def rec(e: Expr)(implicit env: Env): CIR.Expr = e match {
    case UnitLiteral() => CIR.Lit(L.UnitLit)
    case BooleanLiteral(v) => CIR.Lit(L.BoolLit(v))
    case IntLiteral(v) => CIR.Lit(L.IntLit(v))
    case CharLiteral(v) => CIR.Lit(L.CharLit(v))
    case StringLiteral(v) => CIR.Lit(L.StringLit(v))

    case Block(es, last) => CIR.buildBlock((es :+ last) map rec)

    case Variable(id) => buildBinding(id)

    case Let(x, e, body) => buildLet(x, e, body, isVar = false)
    case LetVar(x, e, body) => buildLet(x, e, body, isVar = true)

    case Assignment(id, expr) => CIR.Assign(buildBinding(id), rec(expr))

    case FieldAssignment(obj, fieldId, expr) =>
      CIR.Assign(CIR.FieldAccess(rec(obj), rec(fieldId)), rec(expr))

    case LetDef(_, body) =>
      // We don't have to traverse the nested function now because we already have their respective context.
      rec(body)

    case FunctionInvocation(tfd, args0) =>
      val fun = rec(tfd)
      val extra = ctxDB(tfd.fd) map convertVarInfoToParam
      val args = args0 map rec

      CIR.App(fun, extra, args)

    case CaseClass(cct, args0) =>
      val clazz = rec(cct)
      val args = args0 map rec

      CIR.Construct(clazz, args)

    case CaseClassSelector(_, obj, fieldId) => CIR.FieldAccess(rec(obj), rec(fieldId))

    case tuple @ Tuple(args0) =>
      val clazz = tuple2Class(tuple.getType)
      val args = args0 map rec

      CIR.Construct(clazz, args)

    case TupleSelect(tuple, idx) =>
      CIR.FieldAccess(rec(tuple), "_" + idx)

    case ArrayLength(array) => CIR.ArrayLength(rec(array))

    case ArraySelect(array, index) => CIR.ArrayAccess(rec(array), rec(index))

    case ArrayUpdate(array, index, value) =>
      CIR.Assign(CIR.ArrayAccess(rec(array), rec(index)), rec(value))

    case array @ NonemptyArray(empty, Some((value0, length0))) if empty.isEmpty =>
      val arrayType = rec(array.getType).asInstanceOf[CIR.ArrayType]
      val value = rec(value0)

      // Convert to VLA or normal array
      val alloc = rec(length0) match {
        case CIR.Lit(L.IntLit(length)) =>
          val values = (0 until length) map { _ => value } // the same expression, != same runtime value
          CIR.ArrayAllocStatic(arrayType, length, values)

        case length =>
          if (arrayType.base.containsArray)
            fatalError(s"VLAs cannot have elements being/containing other array", array.getPos)

          warning(s"VLAs should be avoid according to MISRA C rules", array.getPos)

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

      val alloc = CIR.ArrayAllocStatic(arrayType, values.length, values)
      CIR.ArrayInit(alloc)


    case IfExpr(cond, thenn, NoTree(_)) => CIR.If(rec(cond), rec(thenn))
    case IfExpr(cond, thenn, elze) => CIR.IfElse(rec(cond), rec(thenn), rec(elze))

    case While(cond, body) => CIR.While(rec(cond), rec(body))

    case LessThan(lhs, rhs)       => buildBinOp(lhs, O.LessThan, rhs)
    case GreaterThan(lhs, rhs)    => buildBinOp(lhs, O.GreaterThan, rhs)
    case LessEquals(lhs, rhs)     => buildBinOp(lhs, O.LessEquals, rhs)
    case GreaterEquals(lhs, rhs)  => buildBinOp(lhs, O.GreaterEquals, rhs)
    case Equals(lhs, rhs)         => buildBinOp(lhs, O.Equals, rhs)
    case Not(Equals(lhs, rhs))    => buildBinOp(lhs, O.NotEquals, rhs)

    case Not(rhs)                 => buildUnOp(O.Not, rhs)
    case And(exprs)               => buildMultiOp(O.And, exprs)
    case Or(exprs)                => buildMultiOp(O.Or, exprs)

    case BVPlus(lhs, rhs)         => buildBinOp(lhs, O.Plus, rhs)
    case BVMinus(lhs, rhs)        => buildBinOp(lhs, O.Minus, rhs)
    case BVUMinus(rhs)            => buildUnOp(O.UMinus, rhs)
    case BVTimes(lhs, rhs)        => buildBinOp(lhs, O.Times, rhs)
    case BVDivision(lhs, rhs)     => buildBinOp(lhs, O.Div, rhs)
    case BVRemainder(lhs, rhs)    => buildBinOp(lhs, O.Modulo, rhs)
    case BVNot(rhs)               => buildUnOp(O.BNot, rhs)
    case BVAnd(lhs, rhs)          => buildBinOp(lhs, O.BAnd, rhs)
    case BVOr(lhs, rhs)           => buildBinOp(lhs, O.BOr, rhs)
    case BVXOr(lhs, rhs)          => buildBinOp(lhs, O.BXor, rhs)
    case BVShiftLeft(lhs, rhs)    => buildBinOp(lhs, O.BLeftShift, rhs)
    case BVAShiftRight(lhs, rhs)  => buildBinOp(lhs, O.BRightShift, rhs)
    case BVLShiftRight(lhs, rhs)  => fatalError("Operator >>> is not supported", e.getPos)

    case MatchExpr(scrutinee, cases) => convertPatMap(scrutinee, cases)
    case IsInstanceOf(expr, ct) => CIR.IsA(rec(expr), CIR.ClassType(rec(ct)))
    case AsInstanceOf(expr, ct) => CIR.AsA(rec(expr), CIR.ClassType(rec(ct)))

    case e => internalError(s"expression `$e` of type ${e.getClass} not handled")
  }

}

