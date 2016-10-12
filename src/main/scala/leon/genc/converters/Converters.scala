/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package converters

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps
import purescala.Types._
import xlang.Expressions._
// NOTE don't import CAST._ to decrease possible confusion between the two ASTs

import ExtraOps._

private[genc] trait Converters
extends GenericConverter with FunConverter with ClassConverter with ProgConverter {
  this: CConverter =>

  override def convert(tree: Tree)(implicit funCtx: FunCtx): CAST.Tree = {
    implicit val pos = tree.getPos

    tree match {
      /* ---------------------------------------------------------- Types ----- */
      case CharType    => CAST.Char
      case Int32Type   => CAST.Int32
      case BooleanType => CAST.Bool
      case UnitType    => CAST.Void

      case StringType  => CAST.String

      case IntegerType => CAST.unsupported(s"BigInt")

      case ArrayType(base) =>
        val array = CAST.Array(convertToType(base))
        getType(array.id) getOrElse {
          registerType(array)
          array
        }

      case TupleType(bases) =>
        val tuple = CAST.Tuple(bases map convertToType)
        getType(tuple.id) getOrElse {
          registerType(tuple)
          tuple
        }

      case cd: ClassDef => convertClass(cd)
      case CaseClassType(cd, _) => convertClass(cd)
      case AbstractClassType(cd, _) => convertClass(cd)


      /* ------------------------------------------------------- Literals ----- */
      case CharLiteral(c)    => CAST.Literal(c)
      case IntLiteral(v)     => CAST.Literal(v)
      case BooleanLiteral(b) => CAST.Literal(b)
      case UnitLiteral()     => CAST.Literal(())
      case StringLiteral(s)  => CAST.Literal(s)

      case InfiniteIntegerLiteral(_) => CAST.unsupported("BigInt")


      /* ------------------------------------ Definitions and Statements  ----- */
      case id: Identifier => CAST.Id(id.uniqueName)

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
        CAST.unsupported("NonemptyArray with non empty elements")

      case NonemptyArray(elems, None) => // Here elems is non-empty
        // Sort values according the the key (aka index)
        val indexes = elems.keySet.toSeq.sorted
        val values  = indexes map { elems(_) }

        // Assert all types are the same
        val types   = values map { e => convertToType(e.getType) }
        val typ     = types(0)
        val allSame = types forall { _ == typ }
        if (!allSame) CAST.unsupported("Heterogenous arrays")

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

      case CaseClass(typ, args) =>
        debug(s"CaseClass($typ, $args)")
        instanciateCaseClass(typ.classDef, args)

      case CaseClassSelector(_, x1, fieldId) =>
        val struct = convertToStruct(x1.getType)
        val x2     = convertToStmt(x1)

        val fs = normaliseExecution((x2, struct) :: Nil)
        val x  = fs.values.head

        fs.bodies ~~ CAST.AccessField(x, convertToId(fieldId))

      case LessThan(lhs, rhs)       => buildBinOp(lhs, "<",  rhs)
      case GreaterThan(lhs, rhs)    => buildBinOp(lhs, ">",  rhs)
      case LessEquals(lhs, rhs)     => buildBinOp(lhs, "<=", rhs)
      case GreaterEquals(lhs, rhs)  => buildBinOp(lhs, ">=", rhs)
      case Equals(lhs, rhs)         => buildBinOp(lhs, "==", rhs)

      case Not(rhs)                 => buildUnOp (     "!",  rhs)

      case And(exprs)               => buildMultiOp("&&", exprs)
      case Or(exprs)                => buildMultiOp("||", exprs)

      case BVPlus(lhs, rhs)         => buildBinOp(lhs, "+",  rhs)
      case BVMinus(lhs, rhs)        => buildBinOp(lhs, "-",  rhs)
      case BVUMinus(rhs)            => buildUnOp (     "-",  rhs)
      case BVTimes(lhs, rhs)        => buildBinOp(lhs, "*",  rhs)
      case BVDivision(lhs, rhs)     => buildBinOp(lhs, "/",  rhs)
      case BVRemainder(lhs, rhs)    => buildBinOp(lhs, "%",  rhs)
      case BVNot(rhs)               => buildUnOp (     "~",  rhs)
      case BVAnd(lhs, rhs)          => buildBinOp(lhs, "&",  rhs)
      case BVOr(lhs, rhs)           => buildBinOp(lhs, "|",  rhs)
      case BVXOr(lhs, rhs)          => buildBinOp(lhs, "^",  rhs)
      case BVShiftLeft(lhs, rhs)    => buildBinOp(lhs, "<<", rhs)
      case BVAShiftRight(lhs, rhs)  => buildBinOp(lhs, ">>", rhs)
      case BVLShiftRight(lhs, rhs)  => CAST.unsupported("Operator >>>")

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

        if (cond.isPureValue) CAST.While(cond, body)
        else {
          // Transform while (cond) { body } into
          // while (true) { if (cond) { body } else { break } }
          val condF  = flatten(cond)
          val ifelse = condF.body ~~ buildIfElse(condF.value, CAST.NoStmt, CAST.Break)
          CAST.While(CAST.True, ifelse ~ body)
        }

      case FunctionInvocation(tfd @ TypedFunDef(fd, _), stdArgs) =>
        // Make sure fd is not annotated with cCode.drop
        if (fd.annotations contains "cCode.drop") {
          CAST.unsupported(s"Calling a function annoted with @cCode.drop")
        }

        // Make sure the called function will be defined at some point
        collectIfNeeded(fd)

        // In addition to regular function parameters, add the callee's extra parameters
        val id        = convertToId(fd.id)
        val types     = tfd.params map { p => convertToType(p.getType) }
        val fs        = convertAndNormaliseExecution(stdArgs, types)
        val extraArgs = funCtx.toArgs(getFunExtraArgs(id))
        val args      = extraArgs ++ fs.values

        fs.bodies ~~ CAST.Call(id, args)


      case _: StringConcat => CAST.unsupported("String manipulations")

      case m: MatchExpr =>
        val rewrite = ExprOps.matchToIfThenElse(m)
        convert(rewrite)

      case IsInstanceOf(expr, ct) => convertIsInstanceOf(expr, ct.classDef)
      case AsInstanceOf(expr, ct) => convertAsInstanceOf(expr, ct.classDef)

      case e @ Error(typ, desc) =>
        debug(s"WARNING: `$e` is currently ignored")
        CAST.NoStmt

      case unsupported =>
        CAST.unsupported(s"$unsupported (of type ${unsupported.getClass})")
    }
  }
}

