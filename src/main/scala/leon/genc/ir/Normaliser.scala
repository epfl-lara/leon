/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package ir

import PrimitiveTypes.{ PrimitiveType => PT, _ } // For desambiguation
import Literals._
import Operators._
import IRs._

/*
 * Flatten out block expressions in argument-like position (e.g. function argument, while
 * condition, ...) and ensure execution order match between Scala & C execution models by
 * adding explicit execution points.
 */
final class Normaliser(val ctx: LeonContext) extends Transformer(RIR, NIR) with MiniReporter with NoEnv {
  import from._

  // Inject return in functions that need it
  override def recImpl(fd: FunDef)(implicit env: Env): to.FunDef = super.recImpl(fd) match {
    case fd @ to.FunDef(_, returnType, _, _, to.FunBodyAST(body)) if !isUnitType(returnType) =>
      val newBody = to.FunBodyAST(inject({ e => to.Return(e) })(body))

      fd.body = newBody

      fd

    case fun => fun
  }

  private def recAT(typ: ArrayType)(implicit env: Env) = rec(typ).asInstanceOf[to.ArrayType]
  private def recCT(typ: ClassType)(implicit env: Env) = rec(typ).asInstanceOf[to.ClassType]

  override def recImpl(e: Expr)(implicit env: Env): (to.Expr, Env) = e match {
    case _: Binding | _: Lit | _: Block | _: Deref  => super.recImpl(e)

    case DeclInit(vd0, ArrayInit(alloc0)) =>
      val vd = rec(vd0)

      val (preAlloc, alloc) = alloc0 match {
        case ArrayAllocStatic(typ, length, values0) =>
          val (preValues, values) = flattens(values0)
          val alloc = to.ArrayAllocStatic(recAT(typ), length, values)

          preValues -> alloc

        case ArrayAllocVLA(typ, length0, valueInit0) =>
          val (preLength, length) = flatten(length0)
          val (preValueInit, valueInit) = flatten(valueInit0)

          if (preValueInit.nonEmpty)
            fatalError(s"VLA elements cannot be initialised with a complex expression")

          val alloc = to.ArrayAllocVLA(recAT(typ), length, valueInit)

          preLength -> alloc
      }

      val declinit = to.DeclInit(vd, to.ArrayInit(alloc))

      combine(preAlloc :+ declinit) -> env

    case DeclInit(vd0, value0) =>
      val vd = rec(vd0)
      val (pre, value) = flatten(value0)

      val declinit = to.DeclInit(vd, value)

      combine(pre :+ declinit) -> env

    case App(fd0, extra0, args0) =>
      val fd = rec(fd0)
      val extra = extra0 map rec // context argument are trivial enough to not require special handling
      val (preArgs, args) = flattens(args0)
      val app = to.App(fd, extra, args)

      combine(preArgs :+ app) -> env

    case Construct(cd0, args0) =>
      val cd = rec(cd0)
      val (preArgs, args) = flattens(args0)
      val ctor = to.Construct(cd, args)

      combine(preArgs :+ ctor) -> env

    case ai @ ArrayInit(_) => super.recImpl(ai) // this will be handled later

    case FieldAccess(objekt0, fieldId) =>
      val (preObjekt, objekt) = flatten(objekt0)
      val access = to.FieldAccess(objekt, fieldId)

      combine(preObjekt :+ access) -> env

    case ArrayAccess(array0, index0) =>
      val (preArray, array) = flatten(array0)
      val (preIndex, index) = flatten(index0)
      val access = to.ArrayAccess(array, index)

      combine(preArray ++ preIndex :+ access) -> env

    case ArrayLength(array0) =>
      val (preArray, array) = flatten(array0)
      val length = to.ArrayLength(array)

      combine(preArray :+ length) -> env

    case Assign(lhs0, rhs0) =>
      val (preLhs, lhs) = flatten(lhs0)
      val (preRhs, rhs) = flatten(rhs0)
      val assign = to.Assign(lhs, rhs)

      combine(preLhs ++ preRhs :+ assign) -> env

    case BinOp(op, lhs0, rhs0) =>
      val (preLhs, lhs) = flatten(lhs0)
      val (preRhs, rhs) = flatten(rhs0)

      def default = {
        val binop = to.BinOp(op, lhs, rhs)
        combine(preLhs ++ preRhs :+ binop) -> env
      }

      def short(thenn: to.Expr, elze: to.Expr) = {
        val expr = to.IfElse(lhs, thenn, elze)
        combine(preLhs :+ expr) -> env
      }

      // Handle short-circuiting
      if (preRhs.isEmpty) default
      else op match {
        case And => short(combine(preRhs :+ rhs), to.False)
        case Or => short(to.True, combine(preRhs :+ rhs))
        case _ => default
      }

    case UnOp(op, expr0) =>
      val (pre, expr) = flatten(expr0)
      val unop = to.UnOp(op, expr)

      combine(pre :+ unop) -> env

    case If(cond0, thenn0) =>
      val (preCond, cond) = flatten(cond0)
      val thenn = rec(thenn0)

      val fi = to.If(cond, thenn)

      combine(preCond :+ fi) -> env

    case IfElse(cond0, thenn0, elze0) =>
      val (preCond, cond) = flatten(cond0)
      val thenn = rec(thenn0)
      val elze = rec(elze0)

      val fi = to.IfElse(cond, thenn, elze)

      combine(preCond :+ fi) -> env

    case While(cond0, body0) =>
      val (preCond, cond) = flatten(cond0)
      val body = rec(body0)

      val loop = preCond match {
        case Seq() => to.While(cond, body)
        case preCond =>
          // Transform while ({ preCond; cond }) { body } into
          // while (true) { preCond; if (cond) { body } else { break } }
          to.While(to.True, to.buildBlock(preCond :+ to.IfElse(cond, body, to.buildBlock(to.Break :: Nil))))
      }

      loop -> env

    case IsA(expr0, ct0) =>
      val ct = recCT(ct0)
      val (preExpr, expr) = flatten(expr0)
      val isa = to.IsA(expr, ct)

      combine(preExpr :+ isa) -> env

    case AsA(expr0, ct0) =>
      val ct = recCT(ct0)
      val (preExpr, expr) = flatten(expr0)
      val asa = to.AsA(expr, ct)

      combine(preExpr :+ asa) -> env

    case Ref(e0) =>
      val (pre, e) = flatten(e0)
      val ref = to.Ref(e)

      combine(pre :+ ref) -> env

    case _ => internalError(s"$e is not handled (${e.getClass}) by the normaliser")
  }

  private def combine(es: Seq[to.Expr]): to.Expr = es match {
    case Seq() => internalError("no argument")
    case Seq(e) => e // don't introduce block if we can
    case es => to.buildBlock(es)
  }

  private def flatten(e: Expr)(implicit env: Env): (Seq[to.Expr], to.Expr) = rec(e) match {
    case to.Block(init :+ last) => normalise(init, last)
    case e => normalise(Seq.empty, e)
  }

  // Extract all "init" together
  private def flattens(es: Seq[Expr])(implicit env: Env): (Seq[to.Expr], Seq[to.Expr]) = {
    val empty = (Seq[to.Expr](), Seq[to.Expr]()) // initS + lastS
    (empty /: es) { case ((inits, lasts), e) =>
      val (init, last) = flatten(e)
      (inits ++ init, lasts :+ last)
    }
  }

  private def normalise(pre: Seq[to.Expr], value: to.Expr): (Seq[to.Expr], to.Expr) = value match {
    case fi0 @ to.IfElse(_, _, _) =>
      val norm = freshNormVal(fi0.getType, isVar = true)
      val decl = to.Decl(norm)
      val binding = to.Binding(norm)
      val fi = inject({ e => to.Assign(binding, e) })(fi0)

      (pre :+ decl :+ fi, binding)

    case app @ to.App(fd, _, _) =>
      // Add explicit execution point by saving the result in a temporary variable
      val norm = freshNormVal(fd.returnType, isVar = false)
      val declinit = to.DeclInit(norm, app)
      val binding = to.Binding(norm)

      (pre :+ declinit, binding)

    case ai @ to.ArrayInit(_) =>
      // Attach the ArrayInit to a DeclInit
      // Go backwards to reuse code from the main recImpl function
      debug(s"going backward on $ai")
      val ai0 = backward(ai)
      val norm = freshNormVal(ai.getType, isVar = false)
      val norm0 = backward(norm)
      val declinit0 = from.DeclInit(norm0, ai0)
      val binding = to.Binding(norm)

      val (preDeclinit, declinit) = flatten(declinit0)(Ø)

      (preDeclinit :+ declinit, binding)

    case to.Assign(_, _) => internalError("unexpected assignement")

    case value => (pre, value)
  }

  // Apply `action` on the AST leaf expressions.
  private def inject(action: to.Expr => to.Expr)(e: to.Expr): to.Expr = {
    val injecter = new Transformer(to, to) with NoEnv { injecter =>
      import injecter.from._

      override def recImpl(e: Expr)(implicit env: Env): (Expr, Env) = e match {
        case Decl(_) | DeclInit(_, _) | Assign(_, _) | While(_, _) =>
          internalError(s"Injecting into unexpected expression: $e")

        case Block(es) => buildBlock(es.init :+ rec(es.last)) -> Ø

        case If(cond, thenn) => If(cond, rec(thenn)) -> Ø

        case IfElse(cond, thenn, elze) => IfElse(cond, rec(thenn), rec(elze)) -> Ø

        case e => action(e) -> Ø // no more recursion here
      }
    }

    injecter(e)
  }

  private def isUnitType(typ: to.Type): Boolean = typ match {
    case to.PrimitiveType(UnitType) => true
    case _ => false
  }

  private def freshNormVal(typ: to.Type, isVar: Boolean) = to.ValDef(freshId("norm"), typ, isVar)

  private def freshId(id: String): to.Id = id + "_" + freshCounter.next(id)

  private val freshCounter = new utils.UniqueCounter[String]()

  private val backward = new Transformer(NIR, RIR) with NoEnv
}

